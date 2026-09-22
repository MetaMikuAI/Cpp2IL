using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// In SSA, an object's runtime type cannot change between two tests of the same value.
internal static class RedundantTypeCheckFolder
{
    internal static bool Run(ISILControlFlowGraph graph)
    {
        if (graph.Instructions.Count(i => i.OpCode is OpCode.TryCast or OpCode.IsInstance) < 2) return false;
        var definitions = graph.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());
        var addressed = graph.Instructions.SelectMany(i => i.Operands).OfType<AddressOf>()
            .Select(a => a.Target).OfType<LocalVariable>().ToHashSet();
        var tests = graph.Blocks.Where(b => b.Successors.Count == 2 && b.Successors[0] != b.Successors[1])
            .Select(b => (Block: b, Branch: b.Instructions.LastOrDefault()))
            .Where(t => t.Branch is { OpCode: OpCode.ConditionalJump, Operands: [Block, _] })
            .Select(t => (t.Block, Branch: t.Branch!, Test: Predicate(t.Branch!.Operands[1], 0)))
            .Where(t => t.Test != null && !addressed.Contains(t.Test.Value.Value)).ToArray();
        var groups = tests.GroupBy(t => (t.Test!.Value.Type, t.Test.Value.Value)).Where(g => g.Count() > 1).ToArray();
        if (groups.Length == 0) return false;
        var dominance = new DominatorInfo(graph);
        var changed = false;
        foreach (var group in groups)
        foreach (var test in group)
        foreach (var guard in group)
        {
            if (test.Block == guard.Block) continue;
            var edge = guard.Block.Successors.FirstOrDefault(s => s.Predecessors.Count == 1
                && s.Predecessors[0] == guard.Block && dominance.Dominates(s, test.Block));
            if (edge == null) continue;
            // A single-entry successor proves which guard edge was taken. A join, or
            // merely a dominating guard block, does not prove its branch outcome.
            var matches = (edge == (Block)guard.Branch.Operands[0]) == guard.Test!.Value.Positive;
            test.Branch.SetOperand(1, new Immediate(matches == test.Test!.Value.Positive ? 1 : 0));
            changed = true;
            break;
        }
        return changed && ConstantBranchFolder.PruneSsa(graph);

        (TypeAnalysisContext Type, LocalVariable Value, bool Positive)? Predicate(IOperand operand, int depth)
        {
            if (depth > 16 || operand is not LocalVariable local || addressed.Contains(local)
                || !definitions.TryGetValue(local, out var definition)) return null;
            if (definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable source] }) return Predicate(source, depth + 1);
            if (definition is { OpCode: OpCode.Not, Operands: [_, var inner] })
                return Predicate(inner, depth + 1) is { } p ? (p.Type, p.Value, !p.Positive) : null;
            if (definition is { OpCode: OpCode.IsInstance, Operands: [_, TypeAnalysisContext type, LocalVariable value] })
                return (type, value, true);
            if (definition is not { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, var left, var right] }) return null;
            if (left is Immediate { Value: 0 }) (left, right) = (right, left);
            if (right is not Immediate { Value: 0 }) return null;
            if (left is LocalVariable result && !addressed.Contains(result) && definitions.TryGetValue(result, out var cast)
                && cast is { OpCode: OpCode.TryCast, Operands: [_, TypeAnalysisContext castType, LocalVariable original] })
                return (castType, original, definition.OpCode == OpCode.CheckNotEqual);
            return Predicate(left, depth + 1) is { } nested
                ? (nested.Type, nested.Value, nested.Positive == (definition.OpCode == OpCode.CheckNotEqual)) : null;
        }
    }
}
