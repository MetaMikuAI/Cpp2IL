using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// A successful runtime type test refines only that SSA value and only on its
// success edge. Keep the cast result so later field offsets use the proven type.
internal static class TypeTestFieldRecovery
{
    internal static bool Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var instructions = graph.Instructions;
        if (!instructions.Any(i => i.OpCode is OpCode.IsInstance or OpCode.TryCast)) return false;
        var groups = instructions.Where(i => i.Destination is LocalVariable).GroupBy(i => (LocalVariable)i.Destination!).ToArray();
        var definitions = groups.Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
        var unstable = groups.Where(g => g.Count() != 1).Select(g => g.Key).ToHashSet();
        unstable.UnionWith(instructions.SelectMany(i => i.Operands).OfType<AddressOf>().Select(a => a.Target).OfType<LocalVariable>());
        var reachable = Reachable(graph.EntryBlock, null);
        var roots = new Dictionary<(LocalVariable, bool), LocalVariable?>();
        // Index unresolved field uses once, rather than scanning every operand for
        // each type guard. Recheck the current base after an earlier guard refines it.
        var uses = new Dictionary<LocalVariable, List<(Block Block, Instruction Instruction, int Index)>>();
        foreach (var block in graph.Blocks.Where(reachable.Contains))
        foreach (var instruction in block.Instructions)
        for (var index = 0; index < instruction.Operands.Count; index++)
            if (instruction.Operands[index] is MemoryOperand { Base: LocalVariable receiver, Index: null, Scale: 0, Addend: > 0 }
                && Root(receiver) is { } root)
            {
                if (!uses.TryGetValue(root, out var accesses)) uses[root] = accesses = [];
                accesses.Add((block, instruction, index));
            }
        var changed = false;
        foreach (var guard in graph.Blocks.Where(reachable.Contains))
        {
            if (guard.Successors.Count != 2 || guard.Successors[0] == guard.Successors[1]
                || guard.Instructions.LastOrDefault() is not { OpCode: OpCode.ConditionalJump, Operands: [Block taken, var condition] }
                || Predicate(condition, 0) is not { } predicate)
                continue;
            var test = predicate.Test;
            var target = (TypeAnalysisContext)test.Operands[1];
            var source = (LocalVariable)test.Operands[2];
            if (target.IsValueType || target.IsInterface
                || target is ReferencedTypeAnalysisContext and not GenericInstanceTypeAnalysisContext
                || source.Type is { IsValueType: true } || Root(source) is not { } root
                || unstable.Any(l => Root(l, allowUnstable: true) == root)) continue;
            var success = predicate.Positive ? taken : guard.Successors.Single(s => s != taken);
            if (success.Predecessors is not [var predecessor] || predecessor != guard) continue;
            if (!uses.TryGetValue(root, out var accesses)) continue;
            var candidates = accesses.Where(c => c.Instruction.Operands[c.Index] is MemoryOperand { Base: LocalVariable receiver }
                && Root(receiver) == root).ToArray();
            if (candidates.Length == 0) continue;
            // Edge dominance without rebuilding quadratic dominator sets: any block
            // reachable while avoiding the success entry is outside the proof's scope.
            var outside = Reachable(graph.EntryBlock, success);
            candidates = candidates.Where(c => !outside.Contains(c.Block)).ToArray();
            if (candidates.Length == 0) continue;
            LocalVariable narrowed;
            if (test.OpCode == OpCode.TryCast)
            {
                narrowed = (LocalVariable)test.Operands[0];
                if (narrowed.Type != null && narrowed.Type != target) continue;
                narrowed.Type ??= target;
            }
            else
            {
                var result = (LocalVariable)test.Operands[0];
                narrowed = new LocalVariable($"typed{method.Locals.Count}", new Register(null, $"TYPE_TEST_{method.Locals.Count}"), target);
                method.Locals.Add(narrowed);
                var check = new Instruction(test.Index, OpCode.CheckNotEqual, result, narrowed, new Immediate(0));
                var testBlock = graph.FindBlockByInstruction(test)!;
                testBlock.Instructions.Insert(testBlock.Instructions.IndexOf(test) + 1, check);
                test.OpCode = OpCode.TryCast;
                test.SetOperands(narrowed, target, source);
                definitions[result] = check;
                definitions[narrowed] = test;
            }
            foreach (var candidate in candidates)
            {
                var memory = (MemoryOperand)candidate.Instruction.Operands[candidate.Index];
                memory.Base = narrowed;
                candidate.Instruction.SetOperand(candidate.Index, memory);
            }
            changed = true;
        }
        return changed;

        LocalVariable? Root(LocalVariable value, bool allowUnstable = false)
        {
            var key = (value, allowUnstable);
            if (roots.TryGetValue(key, out var cached)) return cached;
            var seen = new HashSet<LocalVariable>();
            while (seen.Add(value))
            {
                if (!allowUnstable && unstable.Contains(value)) return roots[key] = null;
                if (!definitions.TryGetValue(value, out var definition)
                    || definition is not { OpCode: OpCode.Move, Operands: [_, LocalVariable copy] }) return roots[key] = value;
                value = copy;
            }
            return roots[key] = null;
        }

        (Instruction Test, bool Positive)? Predicate(IOperand operand, int depth)
        {
            if (depth > 16 || operand is not LocalVariable local || unstable.Contains(local)
                || !definitions.TryGetValue(local, out var definition)) return null;
            if (definition is { OpCode: OpCode.IsInstance, Operands: [_, TypeAnalysisContext, LocalVariable] }) return (definition, true);
            if (definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable copy] }) return Predicate(copy, depth + 1);
            if (definition is { OpCode: OpCode.Not, Operands: [_, var inner] })
                return Predicate(inner, depth + 1) is { } p ? (p.Test, !p.Positive) : null;
            if (definition is not { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, var left, var right] }) return null;
            if (left is Immediate { Value: 0 }) (left, right) = (right, left);
            if (right is not Immediate { Value: 0 }) return null;
            if (left is LocalVariable cast && !unstable.Contains(cast) && definitions.TryGetValue(cast, out var castDefinition)
                && castDefinition is { OpCode: OpCode.TryCast, Operands: [_, TypeAnalysisContext, LocalVariable] })
                return (castDefinition, definition.OpCode == OpCode.CheckNotEqual);
            return Predicate(left, depth + 1) is { } nested
                ? (nested.Test, nested.Positive == (definition.OpCode == OpCode.CheckNotEqual)) : null;
        }
    }

    private static HashSet<Block> Reachable(Block entry, Block? excluded)
    {
        var result = new HashSet<Block>();
        var pending = new Stack<Block>();
        pending.Push(entry);
        while (pending.TryPop(out var block))
            if (block != excluded && result.Add(block))
                foreach (var successor in block.Successors) pending.Push(successor);
        return result;
    }
}
