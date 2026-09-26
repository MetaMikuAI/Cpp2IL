using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A call into the shared body of a method on a generic type, such as <c>List&lt;object&gt;.Add</c> or
/// <c>Nullable&lt;Int32Enum&gt;..ctor</c>, is left unresolved while type resolution runs, so that the
/// caller's <c>MethodInfo*</c> or receiver can name the instantiation the body serves. Type resolution
/// reads the receiver only through copies, so a receiver that reaches the call through a phi, e.g. the
/// address of a stack local taken on several paths, leaves the call unresolved. Every value such a
/// receiver can hold has one type once resolution has run, and that type names the instantiation.
/// Out of SSA, versions of an address-taken local merge into one typed local, which settles receivers
/// a phi still split; type resolution no longer runs then, so a value-type argument nothing else typed
/// takes the parameter's type, as resolution would have given it.
/// </summary>
public static class SharedGenericCallRecovery
{
    public static bool Run(MethodAnalysisContext method, bool afterSsa = false)
    {
        var instructions = method.ControlFlowGraph!.Instructions;
        var definitions = instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).ToDictionary(g => g.Key, g => g.ToList());
        var changed = false;

        foreach (var call in instructions)
        {
            if (!call.IsCall || call.Operands[0] is not Immediate target
                || !method.AppContext.MethodsByAddress.TryGetValue(target.UnsignedValue, out var candidates)
                || candidates is not [ConcreteGenericMethodAnalysisContext
                {
                    IsStatic: false, IsPartialInstantiation: false, MethodGenericParameters.Count: 0,
                    DeclaringType: GenericInstanceTypeAnalysisContext shared,
                } placeholder]
                || !shared.GenericArguments.Any(GenericSharing.IsSharedRepresentative))
                continue;

            var receiverIndex = call.OpCode == OpCode.CallVoid ? 1 : 2;
            if (receiverIndex >= call.Operands.Count
                || ReceiverType(call.Operands[receiverIndex], definitions) is not { } receiverType
                || Specialize(placeholder, shared, receiverType) is not { } resolved)
                continue;

            call.SetOperand(0, resolved);
            method.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(call, resolved);
            if (afterSsa)
                TypeArguments(call, resolved, receiverIndex + 1);
            changed = true;
        }

        return changed;
    }

    private static void TypeArguments(Instruction call, MethodAnalysisContext resolved, int firstArgument)
    {
        for (var i = 0; i < resolved.Parameters.Count && firstArgument + i < call.Operands.Count; i++)
        {
            if (call.Operands[firstArgument + i] is LocalVariable { Type: null } argument
                && resolved.Parameters[i].ParameterType is { IsValueType: true } parameterType and not GenericParameterTypeAnalysisContext)
                argument.Type = parameterType;
        }
    }

    // The one type of every value the receiver can hold, through copies and phis: a typed value, or
    // for a value-type receiver passed by reference, the addressed local.
    private static TypeAnalysisContext? ReceiverType(IOperand receiver, Dictionary<LocalVariable, List<Instruction>> definitions)
    {
        var visited = new HashSet<LocalVariable>();
        var pending = new Stack<IOperand>([receiver]);
        TypeAnalysisContext? found = null;

        while (pending.TryPop(out var operand))
        {
            TypeAnalysisContext? type;
            switch (operand)
            {
                case AddressOf { Target: LocalVariable { Type: { } addressed } }:
                    type = addressed;
                    break;
                case LocalVariable local when definitions.TryGetValue(local, out var assignments)
                    && assignments.All(a => a is { OpCode: OpCode.Phi } or { OpCode: OpCode.Move, Operands: [_, AddressOf or LocalVariable] }):
                    if (visited.Add(local))
                        foreach (var assignment in assignments)
                            foreach (var source in assignment.Operands.Skip(1))
                                pending.Push(source);
                    continue;
                case LocalVariable { Type: { } typed }:
                    type = typed switch
                    {
                        ByRefTypeAnalysisContext byRef => byRef.ElementType,
                        PointerTypeAnalysisContext pointer => pointer.ElementType,
                        _ => typed,
                    };
                    break;
                default:
                    return null;
            }

            if (type == null || found != null && !SameType(found, type))
                return null;
            found = type;
        }

        return found;
    }

    private static bool SameType(TypeAnalysisContext a, TypeAnalysisContext b)
        => ReferenceEquals(a, b)
           || a is GenericInstanceTypeAnalysisContext left && b is GenericInstanceTypeAnalysisContext right
           && ReferenceEquals(left.GenericType, right.GenericType)
           && left.GenericArguments.Count == right.GenericArguments.Count
           && left.GenericArguments.Zip(right.GenericArguments).All(pair => SameType(pair.First, pair.Second));

    private static MethodAnalysisContext? Specialize(ConcreteGenericMethodAnalysisContext placeholder, GenericInstanceTypeAnalysisContext shared, TypeAnalysisContext receiverType)
    {
        for (var type = receiverType; type != null; type = type.BaseType)
        {
            if (type is not GenericInstanceTypeAnalysisContext receiver
                || !ReferenceEquals(receiver.GenericType, shared.GenericType))
                continue;

            // The receiver pins the instantiation, but only one the body at this address can serve.
            if (!GenericSharing.MayServe(shared.GenericArguments, receiver.GenericArguments))
                return null;

            return SameType(receiver, shared)
                ? placeholder
                : new ConcreteGenericMethodAnalysisContext(placeholder.BaseMethodContext, receiver.GenericArguments, []);
        }

        return null;
    }
}
