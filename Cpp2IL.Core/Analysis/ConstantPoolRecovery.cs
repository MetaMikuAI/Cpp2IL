using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// ARM64 code loads floating-point constants (and 64-bit integers that no MOV sequence builds cheaply)
/// from a literal pool in read-only data: adrp + ldr s0/d0/x0, [page + offset]. Such a load of a constant
/// address in read-only memory is the value stored there, so it becomes that literal instead of an
/// unmanaged memory load. Only exact reads are taken: 4 or 8 bytes into a floating-point register (a
/// float or a double) and 8 bytes into an integer register; a 4-byte integer load may sign-extend.
/// </summary>
public static class ConstantPoolRecovery
{
    public static void Run(MethodAnalysisContext method, List<Instruction> instructions)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet)
            return;

        var binary = method.AppContext.Binary;
        foreach (var instruction in instructions)
        {
            if (instruction is not { OpCode: OpCode.Move, Operands: [Register { Name: { } name }, MemoryOperand { IsConstant: true, Addend: var address, AccessSize: var size }] }
                || size is not (4 or 8) || address <= 0)
                continue;

            var floating = name.StartsWith('V');
            if (!floating && (size != 8 || !name.StartsWith('X')))
                continue;

            var start = (ulong)address;
            if (!binary.TryMapVirtualAddressToRaw(start, out var raw) || raw < 0 || raw > binary.RawLength - size
                || !binary.IsVirtualAddressReadOnly(start) || !binary.IsVirtualAddressReadOnly(start + (ulong)size - 1))
                continue;

            var bytes = binary.GetRawBinaryContent().Slice((int)raw, size);
            IOperand literal = (floating, size) switch
            {
                (true, 4) => new FloatLiteral(BitConverter.Int32BitsToSingle(BinaryPrimitives.ReadInt32LittleEndian(bytes))),
                (true, 8) => new DoubleLiteral(BitConverter.Int64BitsToDouble(BinaryPrimitives.ReadInt64LittleEndian(bytes))),
                _ => new Immediate(BinaryPrimitives.ReadInt64LittleEndian(bytes)),
            };
            instruction.SetOperand(1, literal);
        }
    }
}
