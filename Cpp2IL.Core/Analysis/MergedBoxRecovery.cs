using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Recovers boxes the compiler tail-merged: predecessors each set up a class and the address of a value
/// and jump to one shared boxing call, so both arguments reach it through phis. Each edge then boxes its
/// own class and value. Equal classes box once, from a phi of the values; differing classes are boxed
/// on their edges and the objects merged instead.
/// </summary>
internal static class MergedBoxRecovery
{
    internal static bool Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not { } graph)
            return false;
        SsaFacts? facts = null;
        var changed = false;
        foreach (var block in graph.Blocks.ToList())
            for (var index = 0; index < block.Instructions.Count; index++)
            {
                var call = block.Instructions[index];
                if (call is not { OpCode: OpCode.Call, Operands: [StringLiteral { Value: var name }, LocalVariable result, var klass, var address, ..] }
                    || !KeyFunctionRecovery.BoxFunctions.Contains(name))
                    continue;
                // Only phis may precede the call, so each value is still what its predecessor left in memory.
                var predecessors = block.Predecessors;
                if (predecessors.Count < 2 || predecessors.Distinct().Count() != predecessors.Count
                    || block.Instructions.Take(index).Any(i => i.OpCode is not (OpCode.Phi or OpCode.Nop)))
                    continue;
                facts ??= new SsaFacts(graph);
                if (Incoming(klass, block) is not { } classes || Incoming(address, block) is not { } addresses)
                    continue;

                var types = classes.Select(c => SsaFacts.ClassConstant(facts.Root(c))).ToList();
                if (types.Any(t => t is not { IsValueType: true } || t is GenericParameterTypeAnalysisContext))
                    continue;
                var values = new List<LocalVariable>();
                for (var edge = 0; edge < predecessors.Count; edge++)
                    if (Value(addresses[edge], types[edge]!) is { } value)
                        values.Add(value);
                // One location cannot hold values of two different types.
                if (values.Count != predecessors.Count
                    || values.Zip(types).GroupBy(pair => pair.First).Any(g => g.Select(pair => pair.Second).Distinct().Count() > 1))
                    continue;
                foreach (var (value, type) in values.Zip(types))
                    value.Type ??= type;

                if (types.Distinct().Count() == 1)
                    index = BoxOnce(method, block, index, call, result, types[0]!, values);
                else if (!BoxPerEdge(method, predecessors, call, result, types!, values))
                    continue;
                changed = true;
            }
        return changed;

        // One operand per predecessor: a phi of this block supplies them, anything else is the same on every edge.
        List<IOperand>? Incoming(IOperand operand, Block block)
        {
            if (facts!.Root(operand) is LocalVariable local && facts.DefiningInstruction(local) is { OpCode: OpCode.Phi } phi
                && block.Instructions.Contains(phi))
                return phi.Operands.Count == block.Predecessors.Count + 1 ? phi.Operands.Skip(1).ToList() : null;
            return Enumerable.Repeat(operand, block.Predecessors.Count).ToList();
        }

        LocalVariable? Value(IOperand address, TypeAnalysisContext type)
        {
            if (facts!.Root(address) is not AddressOf { Target: LocalVariable slot })
                return null;
            if (slot.Type == null || slot.Type == type)
                return slot;
            // A slot typed by another path through a shared location still holds what was copied into it.
            var seen = new HashSet<LocalVariable>();
            for (var copy = slot; seen.Add(copy);)
            {
                if (copy.Type == type)
                    return copy;
                if (facts.DefiningInstruction(copy) is not { OpCode: OpCode.Move, Operands: [_, LocalVariable source] })
                    break;
                copy = source;
            }
            return null;
        }
    }

    private static int BoxOnce(MethodAnalysisContext method, Block block, int index, Instruction call, LocalVariable result,
        TypeAnalysisContext type, List<LocalVariable> values)
    {
        var value = values[0];
        if (values.Any(v => v != value))
        {
            value = NewLocal(method, "mergedBoxValue", type);
            block.Instructions.Insert(index++, new Instruction(call.Index, OpCode.Phi, [value, ..values]));
        }
        call.OpCode = OpCode.Box;
        call.SetOperands(result, type, value);
        return index;
    }

    private static bool BoxPerEdge(MethodAnalysisContext method, List<Block> predecessors, Instruction call, LocalVariable result,
        List<TypeAnalysisContext> types, List<LocalVariable> values)
    {
        // A box placed at the end of a predecessor must not run on its way anywhere else.
        if (predecessors.Any(p => p.Successors.Count != 1))
            return false;
        var boxes = new List<IOperand>();
        for (var edge = 0; edge < predecessors.Count; edge++)
        {
            var boxed = NewLocal(method, "edgeBox", result.Type);
            var instructions = predecessors[edge].Instructions;
            var at = instructions.Count > 0 && instructions[^1].OpCode == OpCode.Jump ? instructions.Count - 1 : instructions.Count;
            instructions.Insert(at, new Instruction(call.Index, OpCode.Box, boxed, types[edge], values[edge]));
            boxes.Add(boxed);
        }
        call.OpCode = OpCode.Phi;
        call.SetOperands([result, ..boxes]);
        return true;
    }

    private static LocalVariable NewLocal(MethodAnalysisContext method, string name, TypeAnalysisContext? type)
    {
        var local = new LocalVariable($"{name}{method.Locals.Count}", new Register(null, $"{name.ToUpperInvariant()}_{method.Locals.Count}"), type);
        method.Locals.Add(local);
        return local;
    }
}
