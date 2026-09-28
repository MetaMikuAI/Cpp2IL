using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Native code clears a struct it builds on the stack, such as an async method's state machine, member by
/// member before filling it in. Generated IL zero-initializes its locals, so those stores repeat what the
/// local already holds, while naming members the caller cannot access (a builder's or awaiter's private
/// fields). Drops a stack aggregate's member zero stores for as long as nothing else has touched the
/// aggregate on every path from the entry.
/// </summary>
public static class InitialZeroStoreElimination
{
    public static bool Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var aggregates = graph.Blocks.SelectMany(b => b.Instructions).Select(ZeroStoreTarget).OfType<LocalVariable>()
            .Where(l => method.StackAggregates.ContainsKey(l.Register.Number) && !l.IsThis && !method.ParameterLocals.Contains(l))
            .ToHashSet();
        if (aggregates.Count == 0)
            return false;

        // The aggregates still all zero on leaving each block; start from all and shrink to the fixpoint.
        var untouchedOut = graph.Blocks.ToDictionary(b => b, _ => new HashSet<LocalVariable>(aggregates));
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var block in graph.Blocks)
            {
                var state = In(graph, block, untouchedOut, aggregates);
                foreach (var instruction in block.Instructions)
                    Transfer(instruction, state, null);
                if (!state.SetEquals(untouchedOut[block]))
                {
                    untouchedOut[block] = state;
                    changed = true;
                }
            }
        }

        var redundant = new List<Instruction>();
        foreach (var block in graph.Blocks)
        {
            var state = In(graph, block, untouchedOut, aggregates);
            foreach (var instruction in block.Instructions)
                Transfer(instruction, state, redundant);
        }
        foreach (var store in redundant)
        {
            store.OpCode = OpCode.Nop;
            store.SetOperands();
        }
        return redundant.Count != 0;
    }

    private static HashSet<LocalVariable> In(ISILControlFlowGraph graph, Block block,
        Dictionary<Block, HashSet<LocalVariable>> untouchedOut, HashSet<LocalVariable> aggregates)
    {
        if (block == graph.EntryBlock)
            return new HashSet<LocalVariable>(aggregates);
        // A block nothing reaches, such as an exception handler, may run after anything.
        if (block.Predecessors.Count == 0)
            return [];
        var state = new HashSet<LocalVariable>(untouchedOut[block.Predecessors[0]]);
        foreach (var predecessor in block.Predecessors.Skip(1))
            state.IntersectWith(untouchedOut[predecessor]);
        return state;
    }

    private static void Transfer(Instruction instruction, HashSet<LocalVariable> untouched, List<Instruction>? redundant)
    {
        if (untouched.Count == 0)
            return;
        if (ZeroStoreTarget(instruction) is { } target && untouched.Contains(target))
        {
            redundant?.Add(instruction);
            return;
        }
        foreach (var used in DeadCodeEliminator.UsedLocals(instruction))
            untouched.Remove(used);
        if (instruction.Destination is LocalVariable written)
            untouched.Remove(written);
    }

    // The aggregate whose member a zero store clears.
    private static LocalVariable? ZeroStoreTarget(Instruction instruction)
        => instruction is { OpCode: OpCode.Move, Operands: [FieldReference { IsStatic: false, Local: var owner }, Immediate { Value: 0 }] }
            ? owner : null;
}
