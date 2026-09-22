using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Reconstitute an inlined constructor only when both its complete native body and
// the allocation site's straight-line initialization prove the same single store.
internal static class SingleFieldConstructorRecovery
{
    internal static void Run(MethodAnalysisContext context)
    {
        if (context.AppContext.InstructionSet is not NewArmV8InstructionSet || context.ControlFlowGraph is not { } graph) return;
        foreach (var allocation in graph.Instructions)
        {
            if (allocation is not { OpCode: OpCode.Newobj, Operands: [LocalVariable receiver, TypeAnalysisContext type] }
                || type.IsValueType || type is GenericInstanceTypeAnalysisContext || type.GenericParameters.Count != 0
                || type.NestedTypes.Count != 0) continue;
            var next = Following(graph, allocation).Take(2).ToArray();
            if (next is not [
                { OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: ".ctor", IsStatic: false, Parameters.Count: 0 } called, var target] } call,
                { OpCode: OpCode.Move, Operands: [FieldReference field, Immediate value] } store]
                || !ReferenceEquals(target, receiver) || !ReferenceEquals(field.Local, receiver)
                || field.IsNested || field.Field.IsStatic || field.Field.DeclaringType != type
                || field.Offset != field.Field.Offset || field.Field.FieldType.FullName != "System.Int32"
                || type.BaseType != called.DeclaringType || called.UnderlyingPointer == 0) continue;
            var constructors = type.Methods.Where(m => m is { Name: ".ctor", IsStatic: false, Parameters.Count: 1 }
                && m.Parameters[0].ParameterType.FullName == "System.Int32" && m.UnderlyingPointer != 0).ToArray();
            if (constructors is not [{ } constructor]) continue;
            var binary = context.AppContext.Binary;
            if (!binary.TryMapVirtualAddressToRaw(constructor.UnderlyingPointer, out var raw)) continue;
            var bytes = binary.GetRawBinaryContent();
            if (raw < 0 || raw > bytes.Length - 40
                || !binary.TryMapVirtualAddressToRaw(constructor.UnderlyingPointer + 39, out var last) || last != raw + 39) continue;
            if (Decode(bytes.Slice((int)raw, 40), constructor.UnderlyingPointer) is not { } body
                || body.BaseConstructor != called.UnderlyingPointer || body.FieldOffset != field.Offset) continue;
            call.SetOperands(constructor, receiver, value);
            store.OpCode = OpCode.Nop;
            store.SetOperands();
        }
    }

    // Call instructions split blocks. Cross only a unique fall-through edge with
    // a unique predecessor, so no branch can enter the consumed initialization.
    internal static IEnumerable<Instruction> Following(ISILControlFlowGraph graph, Instruction allocation)
    {
        var block = graph.Blocks.First(b => b.Instructions.Contains(allocation));
        var index = block.Instructions.IndexOf(allocation) + 1;
        var visited = new HashSet<Block>();
        while (visited.Add(block))
        {
            for (; index < block.Instructions.Count; index++)
                if (block.Instructions[index].OpCode != OpCode.Nop) yield return block.Instructions[index];
            if (block.Successors is not [{ } successor] || successor.Predecessors.Count != 1) yield break;
            block = successor;
            index = 0;
        }
    }

    internal static (ulong BaseConstructor, int FieldOffset)? Decode(ReadOnlySpan<byte> body, ulong address)
    {
        if (body.Length < 40) return null;
        Span<uint> words = stackalloc uint[10];
        for (var i = 0; i < words.Length; i++) words[i] = BinaryPrimitives.ReadUInt32LittleEndian(body[(i * 4)..]);
        // Save LR/X20/X19; preserve W1 and X0; clear hidden MethodInfo; call base;
        // STR W19,[X20,#offset]; restore precisely the saved registers and return.
        if (words[0] != 0xF81E0FFE || words[1] != 0xA9014FF4 || words[2] != 0x2A0103F3
            || words[3] != 0xAA1F03E1 || words[4] != 0xAA0003F4
            || (words[5] & 0xFC000000) != 0x94000000
            || (words[6] & 0xFFC003FF) != 0xB9000293
            || words[7] != 0xA9414FF4 || words[8] != 0xF84207FE || words[9] != 0xD65F03C0) return null;
        var target = unchecked((ulong)((long)address + 20 + ((int)(words[5] << 6) >> 4)));
        return (target, (int)((words[6] >> 10) & 0xFFF) * 4);
    }
}
