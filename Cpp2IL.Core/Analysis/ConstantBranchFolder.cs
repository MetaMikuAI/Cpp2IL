using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Points branches whose condition folded to a constant at the block they actually reach.
public static class ConstantBranchFolder
{
    public static void Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;

        foreach (var block in graph.Blocks)
        {
            if (block.Instructions.Count == 0)
                continue;

            var branch = block.Instructions[^1];

            if (branch is not { OpCode: OpCode.ConditionalJump, Operands: [_, Immediate condition] })
                continue;

            if (ResolveTarget(branch, graph) is not { } taken)
                continue;

            var destination = condition.Value != 0
                ? taken
                : block.Successors.FirstOrDefault(s => s != taken && s != graph.ExitBlock);

            if (destination == null)
                continue;

            branch.OpCode = OpCode.Jump;
            branch.SetOperands(destination);
        }
    }

    // Unlike the post-SSA folder, this must repair phi inputs as edges disappear.
    internal static bool PruneSsa(ISILControlFlowGraph graph)
    {
        var branches = graph.Blocks.Where(b => b.Successors.Count == 2 && b.Successors[0] != b.Successors[1]
            && b.Instructions.LastOrDefault() is { OpCode: OpCode.ConditionalJump, Operands: [_, Immediate] }).ToList();
        if (branches.Count == 0 || graph.Blocks.Any(b => b.Instructions.Any(i =>
                i.OpCode == OpCode.Phi && i.Operands.Count != b.Predecessors.Count + 1)))
            return false;

        var changed = false;
        foreach (var block in branches)
        {
            var branch = block.Instructions[^1];
            if (ResolveTarget(branch, graph) is not { } taken || !block.Successors.Contains(taken))
                continue;
            var destination = ((Immediate)branch.Operands[1]).Value != 0
                ? taken : block.Successors.Single(s => s != taken);
            foreach (var successor in block.Successors.Where(s => s != destination).ToArray())
                Disconnect(block, successor);
            branch.OpCode = OpCode.Jump;
            branch.SetOperands(destination);
            block.CalculateBlockType();
            changed = true;
        }
        if (!changed) return false;

        var reachable = new HashSet<Block>();
        var pending = new Stack<Block>();
        pending.Push(graph.EntryBlock);
        while (pending.TryPop(out var block))
            if (reachable.Add(block))
                foreach (var successor in block.Successors)
                    pending.Push(successor);

        foreach (var block in graph.Blocks.Where(b => !reachable.Contains(b)
                     && b != graph.EntryBlock && b != graph.ExitBlock).ToList())
        {
            foreach (var successor in block.Successors.ToArray()) Disconnect(block, successor);
            foreach (var predecessor in block.Predecessors.ToArray()) Disconnect(predecessor, block);
            graph.Blocks.Remove(block);
        }
        return true;
    }

    private static void Disconnect(Block predecessor, Block successor)
    {
        var index = successor.Predecessors.IndexOf(predecessor);
        foreach (var phi in successor.Instructions.Where(i => i.OpCode == OpCode.Phi))
            phi.RemoveOperandAt(index + 1);
        successor.Predecessors.RemoveAt(index);
        predecessor.Successors.Remove(successor);
    }

    private static Block? ResolveTarget(Instruction branch, ISILControlFlowGraph graph) => branch.Operands[0] switch
    {
        Block block => block,
        Instruction instruction => graph.FindBlockByInstruction(instruction),
        _ => null,
    };
}
