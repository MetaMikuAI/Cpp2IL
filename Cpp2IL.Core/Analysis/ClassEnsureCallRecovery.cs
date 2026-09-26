using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Removes calls to runtime helpers that make sure a class (or a method's metadata) is initialized and hand
/// the same pointer back (il2cpp's InitFromCodegen and similar, called before an RGCTX class or method is
/// used). That initialization is implicit in managed code, so such a call is just its argument.
/// </summary>
public static class ClassEnsureCallRecovery
{
    private static readonly ConcurrentDictionary<(ApplicationAnalysisContext App, ulong Target), bool> ReturnsArgument = new();

    // Enough of a helper to reach its normal return.
    private const int ScanBytes = 32 * 4;

    public static void Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet)
            return;

        // Uses include the base and index of memory operands (a size read from the returned class).
        var uses = method.ControlFlowGraph!.Instructions.SelectMany(i => i.Operands.Skip(i.Destination != null ? 1 : 0))
            .SelectMany(o => o is MemoryOperand m ? new[] { m.Base, m.Index } : new[] { o })
            .OfType<LocalVariable>().ToHashSet();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            // Only a call whose result goes on to be used: rewriting it leaves a copy behind, whereas a
            // void one would leave its guard's arm empty, which later layout cannot always express.
            const int argumentIndex = 2;
            if (instruction is not { OpCode: OpCode.Call, Operands: [Immediate target, LocalVariable result, ..] }
                || !uses.Contains(result)
                || instruction.Operands.Count <= argumentIndex
                || instruction.Operands[argumentIndex] is not LocalVariable { Type: RuntimeClassTypeAnalysisContext or RuntimeMethodInfoAnalysisContext } klass
                || !IsClassEnsureHelper(method.AppContext, target.UnsignedValue))
                continue;

            // The result is the same class, and must be declared like it
            result.Type = klass.Type;
            instruction.OpCode = OpCode.Move;
            instruction.SetOperands(result, klass);
        }
    }

    private static bool IsClassEnsureHelper(ApplicationAnalysisContext app, ulong target)
        => ReturnsArgument.GetOrAdd((app, target), key =>
        {
            var binary = key.App.Binary;
            // Runtime code only: a managed method returning its argument may still do real work.
            if (key.Target >= key.App.ManagedCodeStart && key.Target <= key.App.ManagedCodeEnd
                || key.App.MethodsByAddress.ContainsKey(key.Target)
                || !binary.TryMapVirtualAddressToRaw(key.Target, out var raw) || raw < 0 || raw > binary.RawLength - ScanBytes)
                return false;
            return ReturnsFirstArgument(binary.GetRawBinaryContent().Slice((int)raw, ScanBytes), key.Target);
        });

    /// <summary>
    /// Whether the code up to its first return saves X0 in a callee-saved register, leaves that register
    /// alone (calls may come in between), and returns it: <c>mov Xs, x0 ... mov x0, Xs; [ldp]; ret</c>.
    /// </summary>
    internal static bool ReturnsFirstArgument(ReadOnlySpan<byte> bytes, ulong address)
    {
        List<Arm64Instruction> code;
        try
        {
            code = Disassembler.Disassemble(bytes, address, new Disassembler.Options(true, true, false)).ToList();
        }
        catch
        {
            return false;
        }

        var ret = code.FindIndex(i => i.Mnemonic == Arm64Mnemonic.RET);
        if (ret < 0)
            return false;
        code = code.Take(ret).ToList();

        var save = code.FindIndex(i => i is { Mnemonic: Arm64Mnemonic.MOV, Op1Reg: Arm64Register.X0 }
            && i.Op0Reg is >= Arm64Register.X19 and <= Arm64Register.X28);
        if (save < 0 || code.Take(save).Any(i => i.Mnemonic is not (Arm64Mnemonic.STP or Arm64Mnemonic.STR or Arm64Mnemonic.SUB)))
            return false;
        var saved = code[save].Op0Reg;

        var restore = code.FindLastIndex(i => i is { Mnemonic: Arm64Mnemonic.MOV, Op0Reg: Arm64Register.X0 });
        if (restore <= save || code[restore].Op1Reg != saved
            || code.Skip(restore + 1).Any(i => i.Mnemonic is not (Arm64Mnemonic.LDP or Arm64Mnemonic.LDR or Arm64Mnemonic.ADD)
                || i.Op0Reg == Arm64Register.X0 || i.Op1Reg == Arm64Register.X0))
            return false;

        // The saved register keeps the argument throughout; stores naming it read it and are fine.
        return code.Skip(save + 1).Take(restore - save - 1).All(i =>
            i.Mnemonic is Arm64Mnemonic.STR or Arm64Mnemonic.STP or Arm64Mnemonic.STRB or Arm64Mnemonic.STRH
                or Arm64Mnemonic.CMP or Arm64Mnemonic.TST or Arm64Mnemonic.CBZ or Arm64Mnemonic.CBNZ
                or Arm64Mnemonic.TBZ or Arm64Mnemonic.TBNZ or Arm64Mnemonic.B or Arm64Mnemonic.BL
            || i.Op0Reg != saved && !(i.Mnemonic is Arm64Mnemonic.LDP && i.Op1Reg == saved));
    }
}
