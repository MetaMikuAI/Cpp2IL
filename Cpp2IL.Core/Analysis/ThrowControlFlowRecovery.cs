using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Analysis;

// Runtime calls become throws after SSA construction. Their old fallthrough edges
// must not feed register values into the code laid out after the native helper.
public static class ThrowControlFlowRecovery
{
    public static void Run(ISILControlFlowGraph cfg)
    {
        var throws = cfg.Blocks.Where(b => b.Instructions.Any(i => i.OpCode == OpCode.Throw)).ToList();
        if (throws.Count == 0) return;
        var predecessors = cfg.Blocks.ToDictionary(b => b, b => b.Predecessors.ToList());
        foreach (var block in throws)
        {
            var index = block.Instructions.FindIndex(i => i.OpCode == OpCode.Throw);
            block.Instructions.RemoveRange(index + 1, block.Instructions.Count - index - 1);
            foreach (var successor in block.Successors)
                successor.Predecessors.Remove(block);
            block.Successors.Clear();
            block.Successors.Add(cfg.ExitBlock);
            cfg.ExitBlock.Predecessors.Add(block);
            block.CalculateBlockType();
        }
        cfg.RemoveUnreachableBlocks();
        foreach (var block in cfg.Blocks)
        {
            var old = predecessors[block];
            foreach (var phi in block.Instructions.Where(i => i.OpCode == OpCode.Phi))
            {
                // Preserve input ordering when removing an edge or an unreachable predecessor.
                for (var i = old.Count - 1; i >= 0; i--)
                    if (!block.Predecessors.Contains(old[i]))
                        phi.RemoveOperandAt(i + 1);
                if (phi.Operands.Count == 2)
                    phi.OpCode = OpCode.Move;
            }
        }
    }
}
