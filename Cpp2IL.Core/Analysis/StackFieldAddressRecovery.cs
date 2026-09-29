using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// The address of a member of a struct on the stack is formed as the struct's address plus the member's
/// offset, or with an OR where the slot's alignment leaves those bits clear (an async method stub's
/// <c>&amp;stateMachine | 8</c> for its builder), likewise from a value type's own this. Read it as the member's
/// address, <c>&amp;stateMachine.&lt;&gt;t__builder</c>.
/// Runs out of SSA.
/// </summary>
public static class StackFieldAddressRecovery
{
    // A struct on the stack whose address is taken, or the struct a value type's method runs on.
    private static (LocalVariable Storage, TypeAnalysisContext Type)? Struct(MethodAnalysisContext method, IOperand based) => based switch
    {
        AddressOf { Target: LocalVariable { Type: { IsValueType: true } type } storage }
            when method.StackAggregates.ContainsKey(storage.Register.Number) || storage.Register.Name.StartsWith("stack_") => (storage, type),
        // A generic owner's own fields are bound to it over its own type parameters, as IL references them.
        LocalVariable { IsThis: true } self when method.DeclaringType is { IsValueType: true } owner
            => (self, owner.GenericParameters.Count == 0 ? owner : new GenericInstanceTypeAnalysisContext(owner, owner.GenericParameters)),
        _ => null,
    };

    public static bool Run(MethodAnalysisContext method)
    {
        var instructions = method.ControlFlowGraph!.Instructions;
        var changed = false;
        foreach (var instruction in instructions)
        {
            if (instruction is not { OpCode: OpCode.Add or OpCode.Or, Operands: [LocalVariable destination, var based, Immediate { Value: > 0 and < 0x1000 } offset] }
                || Struct(method, based) is not ({ } storage, { } type)
                // An OR adds only bits the slot's alignment leaves clear.
                || instruction.OpCode == OpCode.Or && (offset.Value >= 16 || (offset.Value & (offset.Value - 1)) != 0 && offset.Value >= 8)
                || GenericInstanceFieldLayout.ComputeLayout(type) is not { Slots: var slots }
                || slots.FirstOrDefault(s => s.Offset == offset.Value) is not { } slot)
                continue;

            instruction.OpCode = OpCode.Move;
            instruction.SetOperands(destination, new AddressOf(new FieldReference(slot.Field, storage, (int)offset.Value)));
            if (destination.Type is not ByRefTypeAnalysisContext && instructions.Count(i => i.Destination == destination) == 1)
                destination.Type = new ByRefTypeAnalysisContext(slot.Field.FieldType);
            changed = true;
        }
        return changed;
    }
}
