using System;
using System.Collections.Generic;
using System.Linq;
using Disarm;
using Cpp2IL.Core.Logging;
using Cpp2IL.Core.Utils;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Il2CppApiFunctions;

public class NewArm64KeyFunctionAddresses : BaseKeyFunctionAddresses
{
    private static readonly (string Namespace, string Type, string Method)[] WriteBarrierAnchors =
    [
        ("System.Threading.Tasks", "Task`1", "GetAwaiter"),
        ("System.Threading.Tasks", "Task", "GetAwaiter"),
        ("System.Threading", "ExecutionContext", "get_LogicalCallContext"),
        ("System.Threading", "CancellationTokenSource", "get_Token"),
        ("System", "BadImageFormatException", "get_Message"),
    ];

    private List<Arm64Instruction>? _cachedDisassembledBytes;

    /// <summary>
    /// Il2CppClass::initialized_and_no_error, which Runtime::ClassInit tests on entry. Unity 6 reads
    /// the whole 32-bit field; older builds masked a bit out of the flags byte at 0x135.
    /// </summary>
    private const int InitialisedFieldOffset = 0xE4;

    protected override void AttemptInstructionAnalysisToFillGaps()
    {
        // Packers routinely strip the export table down to a handful of entries, and every key
        // function found via FindExport goes with it. Runtime::ClassInit is worth recovering by
        // shape because the whole chain hangs off it: without the export, the thunk that method
        // bodies actually call is never identified either, and every one of those calls is emitted
        // as "method not found" - 43% of all unresolved call targets on the binary this was
        // written against.
        if (il2cpp_runtime_class_init_actual == 0)
            il2cpp_runtime_class_init_actual = FindClassInitByShape();
    }

    /// <summary>
    /// Finds Runtime::ClassInit by its entry test of Il2CppClass::initialized_and_no_error.
    /// </summary>
    /// <remarks>
    /// The instruction pair alone is far too common - 318 sites on the binary this was developed
    /// against - because every inlined class-init guard uses it too. What distinguishes the
    /// function itself is that the test sits within a few instructions of a prologue, since
    /// ClassInit does nothing else first. That narrowed those 318 candidates to exactly one.
    /// </remarks>
    private ulong FindClassInitByShape()
    {
        const int maxInstructionsFromPrologue = 5;

        var disassembly = DisassembleTextSection();
        var found = 0ul;

        for (var i = 1; i < disassembly.Count; i++)
        {
            if (!IsInitialisedFieldTest(disassembly[i - 1], disassembly[i]))
                continue;

            // Walk back to a prologue. Anything further away is a guard inside a larger function.
            for (var back = 1; back <= maxInstructionsFromPrologue && i - 1 - back >= 0; back++)
            {
                if (!IsPrologue(disassembly[i - 1 - back]))
                    continue;

                if (found != 0)
                    return 0; // ambiguous - better to find nothing than the wrong function

                found = disassembly[i - 1 - back].Address;
                break;
            }
        }

        if (found != 0)
            Logger.VerboseNewline($"\tRecovered il2cpp:vm::Runtime::ClassInit by shape at 0x{found:X} (export was stripped)");

        return found;
    }

    /// <summary>LDR Wn, [X0, #0xE4] followed by CBZ on the same register.</summary>
    internal static bool IsInitialisedFieldTest(Arm64Instruction load, Arm64Instruction branch)
        => load is { Mnemonic: Arm64Mnemonic.LDR, Op0Kind: Arm64OperandKind.Register, MemBase: Arm64Register.X0 }
           && load.MemOffset == InitialisedFieldOffset
           && load.MemIndexMode == Arm64MemoryIndexMode.Offset
           && branch is { Mnemonic: Arm64Mnemonic.CBZ }
           && RegisterIndex(branch.Op0Reg) == RegisterIndex(load.Op0Reg);

    /// <summary>Register number, ignoring whether it was named as W or X.</summary>
    private static int RegisterIndex(Arm64Register register) => register switch
    {
        >= Arm64Register.X0 and <= Arm64Register.X31 => register - Arm64Register.X0,
        >= Arm64Register.W0 and <= Arm64Register.W31 => register - Arm64Register.W0,
        _ => -1,
    };

    /// <summary>SUB SP, SP, #imm or STP with a pre-indexed SP - i.e. a frame being set up.</summary>
    internal static bool IsPrologue(Arm64Instruction instruction)
        => instruction.Mnemonic == Arm64Mnemonic.SUB
               && instruction.Op0Reg == Arm64Register.X31 && instruction.Op1Reg == Arm64Register.X31
               && instruction.Op2Kind == Arm64OperandKind.Immediate
           || instruction.Mnemonic == Arm64Mnemonic.STP
               && instruction.MemBase == Arm64Register.X31
               && instruction.MemIndexMode == Arm64MemoryIndexMode.PreIndex;

    private List<Arm64Instruction> DisassembleTextSection()
    {
        if (_cachedDisassembledBytes == null)
        {
            var binary = _appContext.Binary;
            var toDisasm = binary.GetEntirePrimaryExecutableSection();
            _cachedDisassembledBytes = Disassembler.Disassemble(toDisasm, binary.GetVirtualAddressOfPrimaryExecutableSection(), new(true, true, false)).ToList();
        }

        return _cachedDisassembledBytes;
    }

    private HashSet<ulong> CallTargets => field ??=
    [
        .. DisassembleTextSection()
            .Where(i => i.Mnemonic == Arm64Mnemonic.BL)
            .Select(i => i.BranchTarget)
    ];

    private bool IsFunctionStart(List<Arm64Instruction> disassembly, int index)
    {
        if (CallTargets.Contains(disassembly[index].Address))
            return true;

        if (index == 0)
            return true;

        // it's a function start if the previous instruction can't fall through into it
        var previous = disassembly[index - 1];
        return previous.Mnemonic is Arm64Mnemonic.RET or Arm64Mnemonic.RETAA or Arm64Mnemonic.RETAB or Arm64Mnemonic.BR or Arm64Mnemonic.BRK or Arm64Mnemonic.INVALID
               || (previous.Mnemonic == Arm64Mnemonic.B && previous.MnemonicConditionCode is Arm64ConditionCode.NONE or Arm64ConditionCode.AL);
    }

    protected override IEnumerable<ulong> FindAllThunkFunctions(ulong addr, uint maxBytesBack = 0, params ulong[] addressesToIgnore)
    {
        //Disassemble .text
        var disassembly = DisassembleTextSection();

        for (var index = 0; index < disassembly.Count; index++)
        {
            var instruction = disassembly[index];

            // a thunk ends by tail-calling the real function
            if (instruction.Mnemonic != Arm64Mnemonic.B || instruction.MnemonicConditionCode is not (Arm64ConditionCode.NONE or Arm64ConditionCode.AL) || instruction.BranchTarget != addr)
                continue;

            if (addressesToIgnore.Contains(instruction.Address))
                continue;

            // walk back over any setup instructions to the start of the function containing the branch,
            // bailing if it's too far away to be a thunk
            var maxInstructionsBack = (int)(maxBytesBack / 4);
            for (var back = 0; back <= maxInstructionsBack && index - back >= 0; back++)
            {
                if (!IsFunctionStart(disassembly, index - back))
                    continue;

                var start = disassembly[index - back].Address;
                if (!addressesToIgnore.Contains(start))
                    yield return start;

                break;
            }
        }
    }

    protected override ulong FindFirstCallTargetInMethod(ulong methodVa)
    {
        var instructions = NewArm64Utils.GetArm64MethodBodyAtVirtualAddress(_appContext.Binary, methodVa, false);
        var call = instructions.FirstOrDefault(i => i.Mnemonic == Arm64Mnemonic.BL);
        return call.Mnemonic == Arm64Mnemonic.BL ? call.BranchTarget : 0;
    }

    protected override ulong FindMetadataInitInline(ulong metadataInit)
    {
        var directThunk = base.FindMetadataInitInline(metadataInit);
        if (directThunk != 0)
            return directThunk;

        // 较新的 ARM64 构建可能把普通版和 inline 版作为兄弟函数发出：普通版调用共享实现并添加
        // barrier，inline 版则直接尾调用共享实现。
        var implementation = FindFirstCallTargetInMethod(metadataInit);
        return implementation == 0
            ? 0
            : FindAllThunkFunctions(implementation, 0, metadataInit).FirstOrDefault();
    }

    protected override ulong GetObjectIsInstFromSystemType()
    {
        // Modern corlib exposes the icall on RuntimeTypeHandle, not virtual System.Type.
        // Follow only entry-point B thunks and require the returned pointer's bool test.
        foreach (var typeName in new[] { "RuntimeTypeHandle", "Type" })
        {
            var anchor = ReflectionCache.GetType(typeName, "System")?.Methods?.FirstOrDefault(m => m.Name == "IsInstanceOfType");
            if (anchor == null || (anchor.iflags & (ushort)System.Reflection.MethodImplAttributes.InternalCall) == 0)
                continue; // A virtual managed implementation is not the native icall anchor.
            var address = anchor.MethodPointer;
            var seen = new HashSet<ulong>();
            while (address != 0 && seen.Count < 4 && seen.Add(address))
            {
                var body = NewArm64Utils.GetArm64MethodBodyAtVirtualAddress(_appContext.Binary, address, false, 64);
                if (body.FirstOrDefault() is { Mnemonic: Arm64Mnemonic.B, MnemonicConditionCode: Arm64ConditionCode.NONE or Arm64ConditionCode.AL } thunk)
                {
                    address = thunk.BranchTarget;
                    continue;
                }
                var target = FindObjectIsInstTarget(body);
                if (target != 0) return target;
                break;
            }
        }
        return 0;
    }

    // An entry consisting of B alone preserves all arguments and the return value.
    internal static ulong GetBranchThunkTarget(Model.Contexts.ApplicationAnalysisContext context, ulong thunkAddress)
    {
        var raw = context.Binary.MapVirtualAddressToRaw(thunkAddress, false);
        var bytes = context.Binary.GetRawBinaryContent();
        if (raw < 0 || raw > bytes.Length - 4 || context.Binary.IsBigEndian) return 0;
        return DecodeBranchThunk(System.Buffers.Binary.BinaryPrimitives.ReadUInt32LittleEndian(bytes.Slice((int)raw, 4)), thunkAddress);
    }

    internal static ulong DecodeBranchThunk(uint word, ulong thunkAddress)
    {
        if ((word & 0xfc000000) != 0x14000000) return 0;
        var displacement = (int)(word << 6) >> 4;
        return unchecked((ulong)((long)thunkAddress + displacement));
    }

    internal static ulong FindObjectIsInstTarget(IReadOnlyList<Arm64Instruction> body)
    {
        ulong target = 0;
        for (var i = 0; i + 2 < body.Count && body[i].Mnemonic is not (Arm64Mnemonic.RET or Arm64Mnemonic.RETAA or Arm64Mnemonic.RETAB); i++)
        {
            // cmp x0, #0; cset w0, ne. The pointer-returning helper is the preceding BL,
            // not a metadata lookup or an arbitrary last call in a virtual managed body.
            if (body[i].Mnemonic != Arm64Mnemonic.BL
                || body[i + 1] is not { Mnemonic: Arm64Mnemonic.CMP, Op0Reg: Arm64Register.X0, Op1Kind: Arm64OperandKind.Immediate, Op1Imm: 0 }
                || body[i + 2] is not { Mnemonic: Arm64Mnemonic.CSET, Op0Reg: Arm64Register.W0, FinalOpConditionCode: Arm64ConditionCode.NE })
                continue;
            if (target != 0) return 0; // ambiguous anchor
            target = body[i].BranchTarget;
        }
        return target;
    }

    protected override ulong GetWriteBarrier()
    {
        Logger.Verbose("\tLooking for Il2CppCodeGenWriteBarrier via corlib reference-field stores...");

        var votes = new Dictionary<ulong, int>();

        foreach (var (@namespace, typeName, methodName) in WriteBarrierAnchors)
        {
            var method = ReflectionCache.GetType(typeName, @namespace)?.Methods?.FirstOrDefault(m => m.Name == methodName);
            if (method == null || method.MethodPointer == 0)
                continue;

            List<Arm64Instruction> body;
            try
            {
                body = NewArm64Utils.GetArm64MethodBodyAtVirtualAddress(_appContext.Binary, method.MethodPointer);
            }
            catch
            {
                continue;
            }

            foreach (var target in FindWriteBarrierCalls(body).Distinct())
                votes[target] = votes.TryGetValue(target, out var count) ? count + 1 : 1;
        }

        var best = 0ul;
        var bestVotes = 0;
        foreach (var vote in votes)
        {
            if (vote.Value <= bestVotes)
                continue;

            best = vote.Key;
            bestVotes = vote.Value;
        }

        if (best == 0)
        {
            Logger.VerboseNewline("Not found. Write barriers disabled?");
            return 0;
        }

        Logger.VerboseNewline($"Found at 0x{best:X} (found in {bestVotes} of {WriteBarrierAnchors.Length} checked methods)");
        return best;
    }

    private static IEnumerable<ulong> FindWriteBarrierCalls(List<Arm64Instruction> body)
    {
        const int window = 6;

        for (var i = 0; i < body.Count; i++)
        {
            var call = body[i];
            if (call.Mnemonic is not (Arm64Mnemonic.BL or Arm64Mnemonic.B)
                || (call.Mnemonic == Arm64Mnemonic.B && call.MnemonicConditionCode is not (Arm64ConditionCode.NONE or Arm64ConditionCode.AL)))
                continue;

            var start = Math.Max(0, i - window);
            for (var j = start; j < i; j++)
            {
                var store = body[j];
                if (store.Mnemonic is not (Arm64Mnemonic.STR or Arm64Mnemonic.STUR)
                    || store.Op0Kind != Arm64OperandKind.Register
                    || store.Op0Reg is not (>= Arm64Register.X0 and <= Arm64Register.X31))
                    continue;

                yield return call.BranchTarget;
                break;
            }
        }
    }

    protected override ulong FindFunctionThisIsAThunkOf(ulong thunkPtr, bool prioritiseCall = false)
    {
        var instructions = NewArm64Utils.GetArm64MethodBodyAtVirtualAddress(_appContext.Binary, thunkPtr, false);

        var target = prioritiseCall ? Arm64Mnemonic.BL : Arm64Mnemonic.B;
        var matchingCall = instructions.FirstOrDefault(i => i.Mnemonic == target);

        if (matchingCall.Mnemonic == Arm64Mnemonic.INVALID)
        {
            target = target == Arm64Mnemonic.BL ? Arm64Mnemonic.B : Arm64Mnemonic.BL;
            matchingCall = instructions.FirstOrDefault(i => i.Mnemonic == target);
        }

        return matchingCall.Mnemonic != Arm64Mnemonic.INVALID ? matchingCall.BranchTarget : 0;
    }

    protected override int GetCallerCount(ulong toWhere)
    {
        //Disassemble .text
        var disassembly = DisassembleTextSection();

        //Find all jumps to the target address
        return disassembly.Count(i => i.Mnemonic is Arm64Mnemonic.B or Arm64Mnemonic.BL && i.BranchTarget == toWhere);
    }
}
