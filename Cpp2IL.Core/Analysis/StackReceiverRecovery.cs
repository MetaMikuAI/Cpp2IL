using System.Collections.Generic;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// An address formed before a store still observes the slot's value at the call.
// Bind proven scalar stack receivers at their use, before SSA versions the slot.
internal static class StackReceiverRecovery
{
    internal static void Run(MethodAnalysisContext method)
    {
        foreach (var block in method.ControlFlowGraph!.Blocks)
        for (var index = 0; index < block.Instructions.Count; index++)
        {
            var call = block.Instructions[index];
            if (!call.IsCall) continue;
            var target = call.Operands[0] as MethodAnalysisContext;
            if (call.Operands[0] is Immediate address
                && method.AppContext.MethodsByAddress.TryGetValue(address.UnsignedValue, out var candidates)
                && candidates is [{ } unique]) target = unique;
            if (target is not { IsStatic: false, DeclaringType: { } type }
                || type.FullName is not ("System.Int32" or "System.UInt32" or "System.Single"
                    or "System.Int64" or "System.UInt64" or "System.Double")) continue;
            var receiver = call.OpCode == OpCode.Call ? 2 : 1;
            if (call.Operands.Count <= receiver || call.Operands[receiver] is not Register register) continue;
            var budget = 128;
            if (Resolve(block, index, register, [], ref budget) is { } slot)
                call.SetOperand(receiver, new AddressOf(slot));
        }
    }

    private static StackOffset? Resolve(Block block, int end, Register register,
        HashSet<(Block, int)> path, ref int budget)
    {
        if (--budget < 0 || !path.Add((block, register.Number))) return null;
        try
        {
            for (var i = end - 1; i >= 0; i--)
            {
                var instruction = block.Instructions[i];
                if (instruction.IsCall || instruction.OpCode is OpCode.IndirectCall or OpCode.NotImplemented)
                    return null;
                if (instruction.ImplicitDefinition is { } killed && killed.Number == register.Number) return null;
                if (instruction.Destination is not Register destination || destination.Number != register.Number) continue;
                if (instruction is { OpCode: OpCode.Move, Operands: [_, AddressOf { Target: StackOffset slot }] }) return slot;
                if (instruction is { OpCode: OpCode.Move, Operands: [_, Register copy] })
                    return Resolve(block, i, copy, path, ref budget);
                return null;
            }
            if (block.Predecessors.Count == 0) return null;
            StackOffset? result = null;
            foreach (var predecessor in block.Predecessors)
            {
                var incoming = Resolve(predecessor, predecessor.Instructions.Count, register, path, ref budget);
                if (incoming == null || result is { } previous && previous.Offset != incoming.Value.Offset) return null;
                result = incoming;
            }
            return result;
        }
        finally { path.Remove((block, register.Number)); }
    }
}
