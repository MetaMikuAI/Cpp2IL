using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Analysis;

// Native compilers share one tail-call sequence between calls that only differ in the target they
// load: for example two interface calls on different paths that set up their own target and
// arguments, then jump to a common "restore frame; br xN". After SSA the shared jump calls through
// a phi of both targets, which is not one managed call. Giving each such predecessor its own copy
// of the tail keeps every path's target, and the call it belongs to, visible on its own.
//
// Runs on the lifted graph, before stack analysis and SSA, where duplicating a block that only
// leaves the method cannot change what any other block sees.
internal static class SharedTailCallSplitter
{
    // Epilogue restores and argument moves; a longer tail is not a shared call sequence.
    private const int MaxTailInstructions = 24;

    public static bool Run(ISILControlFlowGraph graph)
    {
        var changed = false;
        foreach (var tail in graph.Blocks.ToList())
        {
            if (!IsSharedTail(graph, tail, out var target))
                continue;

            // Each path must load its own target: a value computed above the split point is one call.
            var predecessors = tail.Predecessors.Distinct().ToList();
            if (predecessors.Count < 2 || predecessors.Any(p => !LoadsTarget(p, target)))
                continue;

            // The block falling into the tail keeps it; every jump into it gets its own copy.
            var keep = predecessors.FirstOrDefault(p => !JumpsTo(p, tail)) ?? predecessors[0];
            foreach (var predecessor in predecessors)
            {
                // A conditional jump whose both edges reach the tail cannot tell its paths apart.
                if (predecessor == keep || !JumpsTo(predecessor, tail) || predecessor.Successors.Count(s => s == tail) != 1)
                    continue;
                Redirect(predecessor, tail, Clone(graph, tail));
                changed = true;
            }
        }
        return changed;
    }

    // A block ending in an indirect jump whose target register arrives from its predecessors.
    private static bool IsSharedTail(ISILControlFlowGraph graph, Block block, out Register target)
    {
        target = default;
        if (block == graph.EntryBlock || block == graph.ExitBlock || block.Instructions.Count is 0 or > MaxTailInstructions
            || block.Instructions[^1] is not { OpCode: OpCode.IndirectJump, Operands: [Register jump, ..] }
            || block.Successors.Any(s => s != graph.ExitBlock) || block.Predecessors.Contains(block))
            return false;
        target = jump;
        var number = jump.Number;
        return block.Instructions.Take(block.Instructions.Count - 1)
            .All(i => i.OpCode is not (OpCode.Call or OpCode.CallVoid or OpCode.IndirectCall or OpCode.Invalid or OpCode.NotImplemented)
                && !(i.Destination is Register written && written.Number == number));
    }

    // The last write of target in the predecessor is a load from memory.
    private static bool LoadsTarget(Block predecessor, Register target)
    {
        for (var i = predecessor.Instructions.Count - 1; i >= 0; i--)
        {
            var instruction = predecessor.Instructions[i];
            if (instruction.IsCall || instruction.OpCode == OpCode.IndirectCall)
                return false;
            if (instruction.Destination is Register written && written.Number == target.Number)
                return instruction is { OpCode: OpCode.Move, Operands: [_, MemoryOperand] };
        }
        return false;
    }

    private static bool JumpsTo(Block predecessor, Block tail)
        => predecessor.Instructions.Count > 0
           && predecessor.Instructions[^1] is { OpCode: OpCode.Jump or OpCode.ConditionalJump, Operands: [var jumpTarget, ..] }
           && (ReferenceEquals(jumpTarget, tail.Instructions[0]) || ReferenceEquals(jumpTarget, tail));

    private static Block Clone(ISILControlFlowGraph graph, Block tail)
    {
        var copy = new Block
        {
            ID = graph.Blocks.Max(b => b.ID) + 1,
            BlockType = tail.BlockType,
        };
        foreach (var instruction in tail.Instructions)
            copy.Instructions.Add(new Instruction(instruction.Index, instruction.OpCode, instruction.Operands.ToList())
            {
                NativeAddress = instruction.NativeAddress,
                ImplicitDefinition = instruction.ImplicitDefinition,
                DeclaredArguments = instruction.DeclaredArguments,
            });
        foreach (var successor in tail.Successors)
        {
            copy.Successors.Add(successor);
            successor.Predecessors.Add(copy);
        }
        graph.Blocks.Add(copy);
        return copy;
    }

    private static void Redirect(Block predecessor, Block tail, Block copy)
    {
        var jump = predecessor.Instructions[^1];
        jump.SetOperand(0, jump.Operands[0] is Block ? copy : copy.Instructions[0]);
        predecessor.Successors[predecessor.Successors.IndexOf(tail)] = copy;
        tail.Predecessors.Remove(predecessor);
        copy.Predecessors.Add(predecessor);
    }
}
