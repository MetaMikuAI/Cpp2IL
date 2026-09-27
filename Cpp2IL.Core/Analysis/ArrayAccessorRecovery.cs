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
/// Outlined array element accessors: a bounds check of the index against the array's length, then a load
/// from or store to the element (array + 0x20 + index * size), are array[index] and array[index] = value.
/// Recognised by their bodies, and applied only where the array operand's element size matches.
/// </summary>
public static class ArrayAccessorRecovery
{
    internal enum Kind
    {
        None,
        Get,
        Set,
    }

    private static readonly ConcurrentDictionary<(ApplicationAnalysisContext App, ulong Target), (Kind Kind, int Size)> Helpers = new();

    private const int LengthOffset = 0x18;
    private const int ElementsOffset = 0x20;

    public static bool Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet || method.AppContext.Binary.PointerSizeBytes != 8)
            return false;

        var uses = method.ControlFlowGraph!.Instructions.SelectMany(DeadCodeEliminator.UsedLocals).ToHashSet();
        var changed = false;
        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (instruction is not { OpCode: OpCode.Call, Operands: [Immediate target, LocalVariable result, LocalVariable { Type: SzArrayTypeAnalysisContext arrayType } array, var index, ..] }
                || method.AppContext.MethodsByAddress.ContainsKey(target.UnsignedValue)
                || index is not (LocalVariable or Immediate))
                continue;

            var (kind, size) = Classify(method.AppContext, target.UnsignedValue);
            var elementType = arrayType.ElementType;
            var elementSize = elementType.IsValueType
                ? TypeSizes.UnboxedSize(elementType.IsEnumType && elementType.EnumUnderlyingType is { } underlying ? underlying : elementType, 8)
                : 8;
            if (kind == Kind.None || elementSize != size)
                continue;

            if (kind == Kind.Get)
            {
                instruction.OpCode = OpCode.Move;
                instruction.SetOperands(result, new ArrayAccess(array, index));
                result.Type ??= elementType;
            }
            else if (instruction.Operands.Count > 4 && !uses.Contains(result))
            {
                var value = instruction.Operands[4];
                instruction.OpCode = OpCode.Move;
                instruction.SetOperands(new ArrayAccess(array, index), value);
            }
            else
                continue;
            changed = true;
        }
        return changed;
    }

    private static (Kind Kind, int Size) Classify(ApplicationAnalysisContext app, ulong target) => Helpers.GetOrAdd((app, target), key =>
    {
        var binary = key.App.Binary;
        if (!binary.TryMapVirtualAddressToRaw(key.Target, out var raw) || raw < 0 || raw > binary.RawLength - 48)
            return (Kind.None, 0);
        try
        {
            ReadOnlySpan<byte> bytes = binary.GetRawBinaryContent().Slice((int)raw, 48);
            List<Arm64Instruction> code = Disassembler.Disassemble(bytes, key.Target, new Disassembler.Options(true, true, false)).ToList();
            return Classify(code);
        }
        catch
        {
            return (Kind.None, 0);
        }
    });

    internal static (Kind Kind, int Size) Classify(ReadOnlySpan<byte> bytes, ulong address)
    {
        List<Arm64Instruction> code = Disassembler.Disassemble(bytes, address, new Disassembler.Options(true, true, false)).ToList();
        return Classify(code);
    }

    internal static (Kind Kind, int Size) Classify(List<Arm64Instruction> code)
    {
        var i = 0;
        if (code.Count > 0 && code[0].Mnemonic is Arm64Mnemonic.STR or Arm64Mnemonic.STP)
            i++; // saving the link register for the out-of-range throw
        if (code.Count < i + 6
            || code[i] is not { Mnemonic: Arm64Mnemonic.LDR, MemBase: Arm64Register.X0, MemOffset: LengthOffset } length
            || code[i + 1] is not { Mnemonic: Arm64Mnemonic.CMP, Op0Reg: Arm64Register.W1 } compare || compare.Op1Reg != length.Op0Reg
            || code[i + 2] is not { Mnemonic: Arm64Mnemonic.B, MnemonicConditionCode: Arm64ConditionCode.CS }
            || code[i + 3] is not { Mnemonic: Arm64Mnemonic.ADD, Op1Reg: Arm64Register.X0, Op2Reg: Arm64Register.X1 } address)
            return (Kind.None, 0);

        // Disarm keeps a shifted register's amount in operand 3.
        var shift = address.FinalOpShiftType == Arm64ShiftType.LSL && address.Op3Kind == Arm64OperandKind.Immediate ? address.Op3Imm : 0;
        if (shift is < 0 or > 3)
            return (Kind.None, 0);
        var size = 1 << (int)shift;
        var access = code[i + 4];
        if (access.MemBase != address.Op0Reg || access.MemOffset != ElementsOffset)
            return (Kind.None, 0);

        var width = access.Mnemonic switch
        {
            Arm64Mnemonic.LDRB or Arm64Mnemonic.STRB or Arm64Mnemonic.LDRSB => 1,
            Arm64Mnemonic.LDRH or Arm64Mnemonic.STRH or Arm64Mnemonic.LDRSH => 2,
            Arm64Mnemonic.LDRSW => 4,
            Arm64Mnemonic.LDR or Arm64Mnemonic.STR => access.Op0Reg is >= Arm64Register.W0 and <= Arm64Register.W31 ? 4 : 8,
            _ => 0,
        };
        if (width != size)
            return (Kind.None, 0);

        if (access.Mnemonic is Arm64Mnemonic.LDR or Arm64Mnemonic.LDRB or Arm64Mnemonic.LDRH or Arm64Mnemonic.LDRSB or Arm64Mnemonic.LDRSH or Arm64Mnemonic.LDRSW)
            return access.Op0Reg is Arm64Register.X0 or Arm64Register.W0 && code.Skip(i + 5).Take(2).Any(c => c.Mnemonic == Arm64Mnemonic.RET) ? (Kind.Get, size) : (Kind.None, 0);

        return access.Op0Reg is Arm64Register.X2 or Arm64Register.W2 ? (Kind.Set, size) : (Kind.None, 0);
    }
}
