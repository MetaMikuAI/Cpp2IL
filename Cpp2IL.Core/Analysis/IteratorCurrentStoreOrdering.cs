using System;
using System.Buffers.Binary;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Native scheduling can put Current before independent bookkeeping. ILSpy needs
// Current immediately before the next state assignment to recognize a yield.
internal static class IteratorCurrentStoreOrdering
{
    internal static void Run(MethodAnalysisContext context)
    {
        if (context.AppContext.InstructionSet is not NewArmV8InstructionSet || context.IsStatic
            || context.Name != "MoveNext" || context.Parameters.Count != 0
            || context.ReturnType.FullName != "System.Boolean" || context.DeclaringType is not { } type
            || !type.IsCompilerGeneratedBasedOnCustomAttributes || type.IsValueType
            || !type.InterfaceContexts.Any(i => i.FullName == "System.Collections.IEnumerator")) return;
        var offsets = type.Properties.Where(p => p.Name.EndsWith(".Current") || p.Name == "Current")
            .Select(p => p.Getter).Where(g => g is { IsStatic: false, Parameters.Count: 0 }
                && g.ReturnType.FullName == "System.Object" && g.UnderlyingPointer != 0)
            .Select(g => GetterOffset(g!)).Where(o => o.HasValue).Distinct().ToArray();
        if (offsets is not [{ } offset]) return;
        var fields = type.Fields.Where(f => f.Offset == offset && !f.IsStatic
            && f.Visibility == FieldAttributes.Private && f.FieldType.FullName == "System.Object").ToArray();
        if (fields is not [{ } current]) return;
        foreach (var block in context.ControlFlowGraph!.Blocks) Order(block, current);
    }

    private static int? GetterOffset(MethodAnalysisContext getter)
    {
        var binary = getter.AppContext.Binary;
        if (!binary.TryMapVirtualAddressToRaw(getter.UnderlyingPointer, out var raw)) return null;
        var bytes = binary.GetRawBinaryContent();
        if (raw < 0 || raw > bytes.Length - 8
            || !binary.TryMapVirtualAddressToRaw(getter.UnderlyingPointer + 7, out var last) || last != raw + 7) return null;
        return DecodeGetter(bytes.Slice((int)raw, 8));
    }

    internal static int? DecodeGetter(ReadOnlySpan<byte> body)
    {
        if (body.Length < 8) return null;
        var load = BinaryPrimitives.ReadUInt32LittleEndian(body);
        return (load & 0xFFC003FF) == 0xF9400000
            && BinaryPrimitives.ReadUInt32LittleEndian(body[4..]) == 0xD65F03C0
            ? (int)((load >> 10) & 0xFFF) * 8 : null; // LDR X0,[X0,#offset]; RET
    }

    internal static void Order(Block block, FieldAnalysisContext current)
    {
        var instructions = block.Instructions;
        for (var i = 0; i < instructions.Count; i++)
        {
            if (instructions[i] is not { OpCode: OpCode.Move, Operands: [FieldReference field, var value] }
                || field.Field != current || field.IsNested || field.Offset != current.Offset || !field.Local.IsThis
                || value is not (Immediate { Value: 0 } or LocalVariable)) continue;
            var end = i;
            while (end + 1 < instructions.Count && CanCross(instructions[end + 1], field, value)) end++;
            if (end == i) continue;
            var operands = instructions[i].Operands.ToList();
            var address = instructions[i].NativeAddress;
            // Keep instruction identities and indexes: a branch to the original
            // first instruction must still execute all reordered bookkeeping.
            for (var j = i; j < end; j++)
            {
                instructions[j].OpCode = instructions[j + 1].OpCode;
                instructions[j].SetOperands(instructions[j + 1].Operands.ToList());
                instructions[j].NativeAddress = instructions[j + 1].NativeAddress;
            }
            instructions[end].OpCode = OpCode.Move;
            instructions[end].SetOperands(operands);
            instructions[end].NativeAddress = address;
            i = end;
        }
    }

    private static bool CanCross(Instruction instruction, FieldReference current, IOperand value)
    {
        if (instruction.OpCode == OpCode.Nop) return true;
        if (instruction.OpCode is not (OpCode.Move or OpCode.Add or OpCode.Subtract or OpCode.Multiply)) return false;
        if (instruction.Operands.Count < 2 || instruction.ImplicitDefinition != null) return false;
        if (instruction.Destination is LocalVariable local)
        {
            if (ReferenceEquals(local, value) || local == current.Local || Width(local.Type) == 0) return false;
        }
        else if (instruction is { OpCode: OpCode.Move, Operands: [FieldReference field, var source] })
        {
            // Do not move past the state assignment (an int constant store).
            if (!Independent(field) || field.Field.FieldType.FullName == "System.Int32" && source is Immediate) return false;
        }
        else return false;
        return instruction.Operands.Skip(1).All(o => o switch
        {
            Immediate or FloatLiteral or DoubleLiteral => true,
            LocalVariable l => Width(l.Type) != 0,
            FieldReference f => Independent(f),
            _ => false
        });

        bool Independent(FieldReference other) => !other.IsNested && other.Local == current.Local
            && !other.Field.IsStatic && other.Field.DeclaringType == current.Field.DeclaringType
            && other.Field.Visibility == FieldAttributes.Private && other.Offset == other.Field.Offset
            && Width(other.Field.FieldType) is var width && width != 0
            && (other.Offset + width <= current.Offset || other.Offset >= current.Offset + 8);
    }

    private static int Width(TypeAnalysisContext? type) => type?.FullName switch
    {
        "System.Int32" or "System.UInt32" or "System.Single" => 4,
        "System.Int64" or "System.UInt64" or "System.Double" => 8,
        _ => 0
    };
}
