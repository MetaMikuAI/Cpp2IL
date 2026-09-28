using System.Linq;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A direct call to an instance method that never reads <c>this</c> gets no receiver set up once IL2CPP's C++
/// is optimized: X0 is left holding whatever the previous call used, often a string or a closure. The call
/// then shows a receiver of an unrelated type (<c>((AppRatingDialog)(object)text).OpenRatingThanksDialog()</c>).
/// C# only lets such a call name an instance of the method's class, so when the caller is one (or is a closure
/// or state machine holding one in <c>&lt;&gt;4__this</c>), that instance is the receiver the source used.
/// Only non-virtual callees are rewritten: a virtual dispatch reads its vtable from the receiver, which is then real.
/// </summary>
public static class StaleReceiverRecovery
{
    public static bool Run(MethodAnalysisContext method)
    {
        if (method.IsStatic || method.DeclaringType is not { } caller)
            return false;
        var changed = false;
        LocalVariable? self = null;
        FieldAnalysisContext? outer = null;
        var outerLooked = false;
        foreach (var call in method.ControlFlowGraph!.Instructions)
        {
            if (call.OpCode is not (OpCode.Call or OpCode.CallVoid) || call.Operands.Count == 0
                || call.Operands[0] is not MethodAnalysisContext { IsStatic: false, IsVirtual: false, Name: not ".ctor", DeclaringType: { } declaring })
                continue;
            var receiverIndex = call.OpCode == OpCode.Call ? 2 : 1;
            if (receiverIndex >= call.Operands.Count || call.Operands[receiverIndex] is not LocalVariable { Type: { } receiverType } receiver
                || !(Unrelated(receiverType, declaring) || !receiver.IsThis && CopiedOnlyFromUnrelated(method, receiver, declaring)))
                continue;

            self ??= method.ParameterLocals.FirstOrDefault(l => l.IsThis) ?? NewThis(method, caller);
            if (Assignable(caller, declaring))
            {
                call.SetOperand(receiverIndex, self);
                changed = true;
                continue;
            }
            if (!outerLooked)
            {
                outerLooked = true;
                outer = caller.Name.StartsWith("<") ? caller.Fields.FirstOrDefault(f => f is { IsStatic: false, Name: "<>4__this" }) : null;
            }
            if (outer != null && Assignable(outer.FieldType, declaring))
            {
                call.SetOperand(receiverIndex, new FieldReference(outer, self, outer.Offset));
                changed = true;
            }
        }
        return changed;
    }

    // A local typed for the call but only ever copied from values of unrelated types is the stale register too.
    private static bool CopiedOnlyFromUnrelated(MethodAnalysisContext method, LocalVariable local, TypeAnalysisContext declaring)
    {
        var definitions = method.ControlFlowGraph!.Instructions.Where(i => ReferenceEquals(i.Destination, local)).ToList();
        return definitions.Count > 0 && definitions.All(d => d is { OpCode: OpCode.Move, Operands: [_, LocalVariable { Type: { } source }] }
            && Unrelated(source, declaring));
    }

    private static LocalVariable NewThis(MethodAnalysisContext method, TypeAnalysisContext caller)
    {
        var local = new LocalVariable("this", new Register(null, "this"), caller) { IsThis = true };
        method.Locals.Add(local);
        return local;
    }

    private static bool Plain(TypeAnalysisContext type) => type is not (GenericParameterTypeAnalysisContext or GenericInstanceTypeAnalysisContext
        or ReferencedTypeAnalysisContext) && !type.IsInterface && !type.IsValueType;

    private static bool Assignable(TypeAnalysisContext type, TypeAnalysisContext target) => Plain(type) && Plain(target) && type.IsAssignableTo(target);

    // Both are plain classes and neither derives from the other: no object is both.
    private static bool Unrelated(TypeAnalysisContext receiver, TypeAnalysisContext declaring) => Plain(receiver) && Plain(declaring)
        && receiver.FullName != "System.Object" && !receiver.IsAssignableTo(declaring) && !declaring.IsAssignableTo(receiver);
}
