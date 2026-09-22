using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Analysis;

// Native tail duplication can leave identical decisions on both sides of a removed
// runtime check. Fold only pure, non-escaping computations with identical phi inputs.
public static class EquivalentBranchFolder
{
    internal static bool Run(ISILControlFlowGraph cfg)
    {
        var uses = new Dictionary<LocalVariable, HashSet<Block>>();
        foreach (var block in cfg.Blocks)
            foreach (var local in block.Instructions.SelectMany(DeadCodeEliminator.UsedLocals))
            {
                if (!uses.TryGetValue(local, out var blocks)) uses[local] = blocks = [];
                blocks.Add(block);
            }

        Dictionary<LocalVariable, Instruction>? PureDefinitions(Block block)
        {
            var definitions = new Dictionary<LocalVariable, Instruction>();
            foreach (var instruction in block.Instructions.SkipLast(1))
            {
                if (instruction.OpCode == OpCode.Nop) continue;
                if (instruction.OpCode is not (OpCode.Move or OpCode.And or OpCode.Or or OpCode.Xor or OpCode.Not
                        or (>= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual))
                    || instruction.Destination is not LocalVariable local
                    || instruction.Operands.Skip(1).Any(o => o is not (LocalVariable or Immediate))
                    || uses.TryGetValue(local, out var readers) && readers.Any(b => b != block)
                    || !definitions.TryAdd(local, instruction))
                    return null;
            }
            return definitions;
        }

        var changed = false;
        foreach (var guard in cfg.Blocks)
        {
            if (guard.Successors.Count != 2 || guard.Instructions.LastOrDefault() is not
                { OpCode: OpCode.ConditionalJump } branch) continue;
            var left = guard.Successors[0];
            var right = guard.Successors[1];
            if (left == right || left == guard || right == guard
                || left.Successors.Count != 2 || right.Successors.Count != 2
                || !left.Successors.ToHashSet().SetEquals(right.Successors)
                || left.Instructions.LastOrDefault() is not { OpCode: OpCode.ConditionalJump, Operands: [Block leftTarget, var leftCondition] }
                || right.Instructions.LastOrDefault() is not { OpCode: OpCode.ConditionalJump, Operands: [Block rightTarget, var rightCondition] }
                || PureDefinitions(left) is not { } leftDefs || PureDefinitions(right) is not { } rightDefs)
                continue;
            var leftInverted = StripNot(ref leftCondition, leftDefs);
            var rightInverted = StripNot(ref rightCondition, rightDefs);
            if ((leftTarget != rightTarget) != (leftInverted != rightInverted)
                || !Equal(leftCondition, rightCondition, leftDefs, rightDefs, 32)
                || left.Successors.Any(s => s.Instructions.Where(i => i.OpCode == OpCode.Phi).Any(phi =>
                    phi.Operands.Count != s.Predecessors.Count + 1
                    || !Equals(phi.Operands[s.Predecessors.IndexOf(left) + 1], phi.Operands[s.Predecessors.IndexOf(right) + 1]))))
                continue;
            branch.SetOperand(1, new Immediate(1));
            changed = true;
        }
        return changed && ConstantBranchFolder.PruneSsa(cfg);
    }

    private static bool StripNot(ref IOperand condition, Dictionary<LocalVariable, Instruction> definitions)
    {
        if (condition is LocalVariable local && definitions.TryGetValue(local, out var instruction)
            && instruction is { OpCode: OpCode.Not, Operands: [_, LocalVariable source] }
            && definitions.TryGetValue(source, out var comparison)
            && comparison.OpCode is >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual)
        {
            condition = source;
            return true;
        }
        return false;
    }

    private static bool Equal(IOperand left, IOperand right, Dictionary<LocalVariable, Instruction> leftDefs,
        Dictionary<LocalVariable, Instruction> rightDefs, int depth)
    {
        if (Equals(left, right)) return true;
        if (depth == 0 || left is not LocalVariable l || right is not LocalVariable r
            || l.Type != r.Type || !leftDefs.TryGetValue(l, out var a) || !rightDefs.TryGetValue(r, out var b)
            || a.OpCode != b.OpCode || a.Operands.Count != b.Operands.Count) return false;
        return a.Operands.Skip(1).Zip(b.Operands.Skip(1)).All(pair =>
            Equal(pair.First, pair.Second, leftDefs, rightDefs, depth - 1));
    }
}
