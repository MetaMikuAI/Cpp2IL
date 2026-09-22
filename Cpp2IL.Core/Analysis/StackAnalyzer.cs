using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

public class StackAnalyzer
{
    [DebuggerDisplay("Size = {Size}")]
    private class StackState
    {
        public int Size;
        public StackState Copy() => new() { Size = this.Size };
    }

    private Dictionary<Block, StackState> _inComingState = [];
    private Dictionary<Block, StackState> _outGoingState = [];
    private Dictionary<Instruction, StackState> _instructionState = [];

    /// <summary>
    /// Max allowed count of blocks to visit (-1 for no limit).
    /// </summary>
    public static int MaxBlockVisitCount = 500000; //High enough to not be legitimately hit, but still give up if something loops infinitely.

    public static void Analyze(MethodAnalysisContext method)
    {
        var analyzer = new StackAnalyzer();

        var graph = method.ControlFlowGraph!;
        graph.RemoveUnreachableBlocks(); // Without this indirect jumps (in try catch i think) cause some weird stuff

        analyzer._inComingState = new Dictionary<Block, StackState> { { graph.EntryBlock, new StackState() } };

        analyzer.TraverseGraph(graph.EntryBlock);

        // The exit block has no outgoing state if it was never reached (e.g. every path loops or
        // throws). That's fine - just skip the end-of-method stack balance check in that case.
        if (analyzer._outGoingState.TryGetValue(graph.ExitBlock, out var outDelta) && outDelta.Size != 0)
        {
            var outText = outDelta.Size < 0 ? "-" + (-outDelta.Size).ToString("X") : outDelta.Size.ToString("X");
            method.AddWarning($"Method ends with non empty stack ({outText}), the output could be wrong!");
        }

        analyzer.ResolveFrameAliases(graph);
        analyzer.CorrectOffsets(graph);
        StackBoxingRecovery.Run(method);
        StackAggregateRecovery.Run(method);
        ReplaceStackWithRegisters(method);

        graph.RemoveNops();
        graph.RemoveEmptyBlocks();
    }

    // Track proven prologue frame addresses through the CFG. A restore at the end
    // of a method must kill the alias there, not invalidate earlier accesses globally.
    private void ResolveFrameAliases(ISILControlFlowGraph graph)
    {
        var seeds = new Dictionary<Instruction, int>();
        foreach (var block in graph.EntryBlock.Successors)
            foreach (var instruction in block.Instructions)
            {
                // After a dynamic stack-pointer assignment its absolute offset is unknown.
                if (instruction.Destination is Register { Name: "rsp" or "sp" or "X31" }) break;
                if (!_instructionState.TryGetValue(instruction, out var state)) continue;
                // An arbitrary stack-local address may point into an aggregate. Keep it
                // for typed field recovery rather than flattening it into scalar slots.
                if (instruction is { OpCode: OpCode.Move, Operands: [Register { Name: "X29" or "rbp" or "ebp" }, AddressOf { Target: StackOffset slot }] })
                {
                    var absoluteOffset = (long)state.Size + slot.Offset;
                    if (absoluteOffset is >= int.MinValue and <= int.MaxValue) seeds[instruction] = (int)absoluteOffset;
                }
                else if (instruction is { OpCode: OpCode.Move, Operands: [Register, Register { Name: "rsp" }] })
                    seeds[instruction] = state.Size;
            }
        if (seeds.Count == 0) return;

        var outgoing = new Dictionary<Block, Dictionary<string, int>>();
        var pending = new Queue<Block>();
        pending.Enqueue(graph.EntryBlock);
        while (pending.TryDequeue(out var block))
        {
            var aliases = Incoming(block);
            foreach (var instruction in block.Instructions) Transfer(instruction, aliases);
            if (outgoing.TryGetValue(block, out var previous) && previous.Count == aliases.Count
                && previous.All(p => aliases.TryGetValue(p.Key, out var value) && value == p.Value)) continue;
            outgoing[block] = aliases;
            foreach (var successor in block.Successors) pending.Enqueue(successor);
        }

        // Rewrite only after convergence: a later back-edge can invalidate a frame alias.
        foreach (var block in graph.Blocks)
        {
            var aliases = Incoming(block);
            foreach (var instruction in block.Instructions)
            {
                if (!_instructionState.TryGetValue(instruction, out var state)) continue;
                for (var i = 0; i < instruction.Operands.Count; i++)
                {
                    if (instruction.Operands[i] is not MemoryOperand { Index: null, Scale: 0, Base: Register frame } memory
                        || !aliases.TryGetValue(frame.Name, out var absoluteOffset)
                        || memory.Addend is < int.MinValue or > int.MaxValue) continue;
                    var relativeOffset = (long)absoluteOffset + memory.Addend - state.Size;
                    if (relativeOffset is >= int.MinValue and <= int.MaxValue)
                        instruction.SetOperand(i, new StackOffset((int)relativeOffset, memory.AccessSize));
                }
                Transfer(instruction, aliases);
            }
        }

        Dictionary<string, int> Incoming(Block block)
        {
            Dictionary<string, int>? result = null;
            foreach (var predecessor in block.Predecessors)
            {
                // An unvisited predecessor is initially unknown; revisit when it arrives.
                if (!outgoing.TryGetValue(predecessor, out var state)) continue;
                if (result == null) result = new(state);
                else foreach (var key in result.Keys.ToList())
                    if (!state.TryGetValue(key, out var value) || value != result[key]) result.Remove(key);
            }
            return result ?? new();
        }

        void Transfer(Instruction instruction, Dictionary<string, int> aliases)
        {
            int? offset = seeds.TryGetValue(instruction, out var seed) ? seed : null;
            if (instruction is { OpCode: OpCode.Move, Operands: [Register, Register source] }
                && aliases.TryGetValue(source.Name, out var copied)) offset = copied;
            if (instruction.Destination is Register destination)
            {
                aliases.Remove(destination.Name);
                if (offset.HasValue) aliases[destination.Name] = offset.Value;
            }
            if (instruction.ImplicitDefinition is { } implicitDefinition) aliases.Remove(implicitDefinition.Name);
        }
    }

    private void CorrectOffsets(ISILControlFlowGraph graph)
    {
        foreach (var block in graph.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                if (instruction is { OpCode: OpCode.ShiftStack })
                {
                    // Nop the shift stack instruction
                    instruction.OpCode = OpCode.Nop;
                    instruction.SetOperands();
                    continue;
                }

                int? state = null;

                // Correct offset for stack operands.
                for (var i = 0; i < instruction.Operands.Count; i++)
                {
                    var op = instruction.Operands[i];

                    var slot = op switch
                    {
                        StackOffset direct => direct,
                        AddressOf { Target: StackOffset addressed } => addressed,
                        _ => (StackOffset?)null
                    };

                    if (slot is { } offset)
                    {
                        // This can only be done before modifying any of the instruction operands,
                        // as doing so will make the dictionary lookup impossible.
                        state ??= _instructionState[instruction].Size;

                        var actual = new StackOffset(state.Value + offset.Offset, offset.AccessSize);
                        instruction.SetOperand(i, op is AddressOf ? new AddressOf(actual) : actual);
                    }
                }
            }
        }
    }

    // Traverse the graph and calculate the stack state for each block and instruction
    private void TraverseGraph(Block initialBlock, int initialVisitedBlockCount = 0)
    {
        var blockLevelState = new Stack<(Block, int)>();
        blockLevelState.Push((initialBlock, initialVisitedBlockCount));

        while (blockLevelState.Count > 0)
        {
            var (block, visitedBlockCount) = blockLevelState.Pop();

            // Copy current state
            var incomingState = _inComingState[block];
            var currentState = incomingState.Copy();

            // Process instructions
            foreach (var instruction in block.Instructions)
            {
                _instructionState[instruction] = currentState;

                if (instruction.OpCode == OpCode.ShiftStack)
                {
                    var offset = (int)((Immediate)instruction.Operands[0]).Value;
                    currentState = currentState.Copy();
                    currentState.Size += offset;
                }
                else if (block.Instructions[^1] == instruction && block.BlockType == BlockType.TailCall)
                {
                    // Tail calls clear stack
                    currentState = currentState.Copy();
                    currentState.Size = 0;
                }
            }

            // Tail calls clear stack
            if (block.BlockType == BlockType.TailCall)
                currentState.Size = 0;

            _outGoingState[block] = currentState;

            visitedBlockCount++;

            if (MaxBlockVisitCount != -1 && visitedBlockCount > MaxBlockVisitCount)
                throw new DecompilerException($"Stack state not settling! ({visitedBlockCount} blocks already visited)");

            // Visit successors
            foreach (var successor in block.Successors)
            {
                // Already visited
                if (_inComingState.TryGetValue(successor, out var existingState))
                {
                    if (existingState.Size != currentState.Size)
                    {
                        _inComingState[successor] = currentState.Copy();
                        blockLevelState.Push((successor, visitedBlockCount + 1));
                    }
                }
                else
                {
                    // Set incoming delta and add to queue
                    _inComingState[successor] = currentState.Copy();
                    blockLevelState.Push((successor, visitedBlockCount + 1));
                }
            }
        }
    }

    private static void ReplaceStackWithRegisters(MethodAnalysisContext method)
    {
        var instructions = method.ControlFlowGraph!.Instructions;

        // Replace stack offset operands
        foreach (var instruction in instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                var operand = instruction.Operands[i];

                if (operand is StackOffset offset)
                    instruction.SetOperand(i, new Register(null, NameForSlot(offset)));

                if (operand is AddressOf { Target: StackOffset addressed })
                    instruction.SetOperand(i, new AddressOf(new Register(null, NameForSlot(addressed))));
            }
        }

        // Replace params
        for (var i = 0; i < method.ParameterOperands.Count; i++)
        {
            var parameter = method.ParameterOperands[i];

            if (parameter is StackOffset offset)
                method.ParameterOperands[i] = new Register(null, NameForSlot(offset));
        }
    }

    private static string NameForSlot(StackOffset offset) => offset.Offset < 0 ? $"stack_-{-offset.Offset:X}" : $"stack_{offset.Offset:X}";
}
