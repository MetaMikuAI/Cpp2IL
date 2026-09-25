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

    protected override void FindVirtualDispatchHelpers()
    {
        Logger.Verbose("	Looking for the virtual dispatch helpers via il2cpp_object_get_virtual_method...");

        var binary = _appContext.Binary;
        var address = binary.GetVirtualAddressOfExportedFunctionByName("il2cpp_object_get_virtual_method");
        for (var hops = 0; address != 0 && hops < 4 && GetBranchThunkTarget(address) is var next and not 0; hops++)
            address = next;

        var raw = address == 0 ? -1 : binary.MapVirtualAddressToRaw(address, false);
        var bytes = binary.GetRawBinaryContent();
        if (raw < 0 || raw > bytes.Length - 4)
        {
            Logger.VerboseNewline("Not found");
            return;
        }

        // Object::GetVirtualMethod is short; a fixed window covers it and FindVirtualDispatchHelpers stops at its return.
        var window = bytes.Slice((int)raw, (int)Math.Min(VirtualMethodWindowBytes, (bytes.Length - raw) & ~3L));
        var body = Disassembler.Disassemble(window, address, new Disassembler.Options(true, true, false)).ToList();
        (il2cpp_vm_class_get_interface_invoke_data_slow_path, il2cpp_vm_runtime_get_generic_virtual_method) = FindVirtualDispatchHelpers(body);

        Logger.VerboseNewline($"Found slow path at 0x{il2cpp_vm_class_get_interface_invoke_data_slow_path:X}, generic virtual method at 0x{il2cpp_vm_runtime_get_generic_virtual_method:X}");
    }

    private const long VirtualMethodWindowBytes = 128 * 4;

    // Object::GetVirtualMethod inlines ClassInlines::GetInterfaceInvokeDataFromVTable: its klass->interfaceOffsets
    // scan loop falls through to the slow path call when no entry matches. For a generic method it then leaves
    // with a tail call to Runtime::GetGenericVirtualMethod(vtableSlotMethod, method). Each must be unique.
    internal static (ulong SlowPath, ulong GenericVirtualMethod) FindVirtualDispatchHelpers(IReadOnlyList<Arm64Instruction> body)
    {
        if (body.Count == 0)
            return (0, 0);

        var end = body.Count;
        for (var i = 0; i < body.Count; i++)
        {
            if (body[i].Mnemonic is Arm64Mnemonic.RET or Arm64Mnemonic.RETAA or Arm64Mnemonic.RETAB)
            {
                end = i + 1;
                break;
            }
        }

        var start = body[0].Address;
        var last = body[end - 1].Address;
        var slowPaths = new HashSet<ulong>();
        var tailCalls = new HashSet<ulong>();
        for (var i = 0; i < end; i++)
        {
            var instruction = body[i];
            if (instruction.Mnemonic != Arm64Mnemonic.B)
                continue;

            var conditional = instruction.MnemonicConditionCode is not (Arm64ConditionCode.NONE or Arm64ConditionCode.AL);
            if (conditional && instruction.BranchTarget >= start && instruction.BranchTarget < instruction.Address
                && i + 1 < end && body[i + 1].Mnemonic == Arm64Mnemonic.BL)
                slowPaths.Add(body[i + 1].BranchTarget);
            else if (!conditional && (instruction.BranchTarget < start || instruction.BranchTarget > last))
                tailCalls.Add(instruction.BranchTarget);
        }

        tailCalls.ExceptWith(slowPaths);
        return (slowPaths.Count == 1 ? slowPaths.Single() : 0, tailCalls.Count == 1 ? tailCalls.Single() : 0);
    }

    protected override ulong GetBranchThunkTarget(ulong address) => GetBranchThunkTarget(_appContext, address);

    // An entry consisting of B alone preserves all arguments and the return value.
    internal static ulong GetBranchThunkTarget(Model.Contexts.ApplicationAnalysisContext context, ulong thunkAddress)
    {
        var raw = context.Binary.MapVirtualAddressToRaw(thunkAddress, false);
        var bytes = context.Binary.GetRawBinaryContent();
        if (raw < 0 || raw > bytes.Length - 4 || context.Binary.IsBigEndian) return 0;
        return DecodeBranchThunk(System.Buffers.Binary.BinaryPrimitives.ReadUInt32LittleEndian(bytes.Slice((int)raw, 4)), thunkAddress);
    }

    protected override ulong GetGuardedTailCallTarget(ulong address)
    {
        var raw = _appContext.Binary.MapVirtualAddressToRaw(address, false);
        var bytes = _appContext.Binary.GetRawBinaryContent();
        if (address == 0 || raw < 0 || raw > bytes.Length - 16 || _appContext.Binary.IsBigEndian) return 0;
        var words = new uint[4];
        for (var i = 0; i < 4; i++)
            words[i] = System.Buffers.Binary.BinaryPrimitives.ReadUInt32LittleEndian(bytes.Slice((int)raw + 4 * i, 4));
        return DecodeGuardedTailCall(words, address);
    }

    // ldr wN, [x0, #imm]; cbz wN, +8; ret; b target
    internal static ulong DecodeGuardedTailCall(IReadOnlyList<uint> words, ulong address)
    {
        if (words.Count < 4 || (words[0] & 0xFFC003E0) != 0xB9400000)
            return 0;
        var flag = words[0] & 0x1F;
        if (words[1] != (0x34000040u | flag) || words[2] != 0xD65F03C0)
            return 0;
        return DecodeBranchThunk(words[3], address + 12);
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
