using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A call returning a 16-byte struct of two integer members (a KeyValuePair of references, say) hands the
/// second one back in X1. A call only identified after lifting, like a recovered interface call, did not
/// define X1, so a read of X1 after it still reaches the version from before the call. Compiled code never
/// reads a caller-saved register across a call for its old value, so such a read is the result's second
/// member: make it one of the result, typed as the struct.
/// </summary>
public static class CompositeReturnRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet || method.AppContext.Binary.PointerSizeBytes != 8
            || method.ControlFlowGraph is not { } graph)
            return;

        var dominators = new DominatorInfo(graph);

        var definitions = graph.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
        var blockOf = graph.Blocks.SelectMany(b => b.Instructions.Select(i => (i, b))).ToDictionary(p => p.i, p => p.b);

        foreach (var call in graph.Instructions.ToList())
        {
            if (call is not { OpCode: OpCode.Call, Operands: [MethodAnalysisContext target, LocalVariable { Register.Name: "X0" } result, ..] }
                || SecondMember(target.ReturnType) is not { } second
                || !blockOf.TryGetValue(call, out var callBlock))
                continue;

            // Reads after the call, with no other call in between, of an X1 defined before it.
            var reads = new List<(Instruction Reader, int Operand)>();
            foreach (var reader in graph.Instructions)
            {
                if (reader == call || !blockOf.TryGetValue(reader, out var readerBlock) || !After(call, callBlock, reader, readerBlock))
                    continue;
                for (var i = reader.Destination != null ? 1 : 0; i < reader.Operands.Count; i++)
                    if (reader.Operands[i] is LocalVariable { Register.Name: "X1" } stale && definitions.TryGetValue(stale, out var definition)
                        && blockOf.TryGetValue(definition, out var definitionBlock) && !After(call, callBlock, definition, definitionBlock))
                        reads.Add((reader, i));
            }
            if (reads.Count == 0)
                continue;

            result.Type ??= target.ReturnType;
            if (result.Type != target.ReturnType && result.Type.FullName != target.ReturnType.FullName)
                continue;
            foreach (var (reader, operand) in reads)
                reader.SetOperand(operand, new FieldReference(second, result, 8));
        }

        // Whether b runs after a, reached only through a: later in a's block, or in a block a's dominates,
        // and no call lies between them to own the register instead.
        bool After(Instruction a, Block aBlock, Instruction b, Block bBlock)
        {
            if (aBlock == bBlock)
            {
                var from = aBlock.Instructions.IndexOf(a);
                var to = aBlock.Instructions.IndexOf(b);
                return to > from && !aBlock.Instructions.Skip(from + 1).Take(to - from - 1).Any(i => i.IsCall);
            }
            if (!dominators.Dominates(aBlock, bBlock))
                return false;
            var start = aBlock.Instructions.IndexOf(a);
            if (aBlock.Instructions.Skip(start + 1).Any(i => i.IsCall)
                || bBlock.Instructions.TakeWhile(i => i != b).Any(i => i.IsCall))
                return false;
            for (var current = dominators.ImmediateDominators.GetValueOrDefault(bBlock); current != null && current != aBlock;
                 current = dominators.ImmediateDominators.GetValueOrDefault(current))
                if (current.Instructions.Any(i => i.IsCall))
                    return false;
            return true;
        }
    }

    // The member at offset 8 of a struct made of exactly two integer (non-float) members at 0 and 8.
    private static FieldAnalysisContext? SecondMember(TypeAnalysisContext type)
    {
        if (!type.IsValueType || type.IsEnumType || type is ByRefTypeAnalysisContext or PointerTypeAnalysisContext or GenericParameterTypeAnalysisContext)
            return null;

        List<(FieldAnalysisContext Field, long Offset, long Size)> members;
        if (type is GenericInstanceTypeAnalysisContext)
        {
            if (GenericInstanceFieldLayout.ComputeLayout(type) is not { Complete: true, Slots: var slots })
                return null;
            members = slots.Select(s => (s.Field, s.Offset, s.Size)).ToList();
        }
        else
        {
            if (GenericInstanceFieldLayout.FindFieldAtUnboxedOffset(type, 0) is not { } low
                || GenericInstanceFieldLayout.FindFieldAtUnboxedOffset(type, 8) is not { } high
                || type.Fields.Count(f => !f.IsStatic) != 2)
                return null;
            members = [(low, 0, 8), (high, 8, 8)];
        }

        if (members is not [var first, var second] || first.Offset != 0 || second.Offset != 8 || second.Size is <= 0 or > 8)
            return null;
        static bool IsFloat(TypeAnalysisContext t) => t.Namespace == "System" && t.Name is "Single" or "Double";
        return IsFloat(first.Field.FieldType) || IsFloat(second.Field.FieldType)
               || first.Field.FieldType is { IsValueType: true, IsEnumType: false } && first.Field.FieldType.Namespace != "System"
               || second.Field.FieldType is { IsValueType: true, IsEnumType: false } && second.Field.FieldType.Namespace != "System"
            ? null
            : second.Field;
    }
}
