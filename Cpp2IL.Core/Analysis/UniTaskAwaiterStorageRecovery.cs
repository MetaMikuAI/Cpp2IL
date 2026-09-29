using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A UniTask returned in registers is split into its source and token, and the inlined GetAwaiter stores
/// the pieces into the awaiter's storage; only the source is left of it as the value stored,
/// <c>awaiter = (UniTask.Awaiter)task.source</c>. That store is <c>awaiter = task.GetAwaiter()</c>: the
/// awaiter's only field is the task. Runs out of SSA, where the task's address can be taken.
/// </summary>
public static class UniTaskAwaiterStorageRecovery
{
    public static bool Run(MethodAnalysisContext method)
    {
        var changed = false;
        foreach (var block in method.ControlFlowGraph!.Blocks)
        {
            var straight = InlinedListAddRecovery.StraightLine(block);
            foreach (var store in block.Instructions)
            {
                if (store is not { OpCode: OpCode.Move, Operands: [LocalVariable { Type: { } awaiterType } awaiter, LocalVariable value] }
                    || !IsAwaiter(awaiterType) || value.Type?.FullName == awaiterType.FullName
                    || Task(straight, straight.IndexOf(store), value) is not { } task
                    || task.Type?.FullName != awaiterType.DeclaringType?.FullName && !IsTaskOf(task.Type, awaiterType)
                    || GetAwaiter(task.Type!) is not { } getAwaiter || getAwaiter.ReturnType.FullName != awaiterType.FullName)
                    continue;

                store.OpCode = OpCode.Call;
                store.SetOperands(getAwaiter, awaiter, new AddressOf(task));
                store.DeclaredArguments = 1;
                changed = true;
            }
        }
        return changed;
    }

    // The task whose source the value copies, unchanged since, or the value when it is the task itself.
    private static LocalVariable? Task(List<Instruction> straight, int at, LocalVariable value)
    {
        if (value.Type is { } type && ((type as GenericInstanceTypeAnalysisContext)?.GenericType ?? type).FullName
                is "Cysharp.Threading.Tasks.UniTask" or "Cysharp.Threading.Tasks.UniTask`1")
            return value;
        for (var index = at - 1; index >= 0; index--)
        {
            var instruction = straight[index];
            if (instruction.Destination != value)
                continue;
            switch (instruction)
            {
                case { OpCode: OpCode.Move, Operands: [_, LocalVariable copied] }:
                    value = copied;
                    continue;
                case { OpCode: OpCode.Move, Operands: [_, FieldReference { IsNested: false, Field.Name: "source", Local: { Type: { } } task }] }:
                    // Nothing in between writes the task.
                    return straight.Skip(index + 1).Take(at - index - 1).Any(i => i.Destination == task
                            || i.Operands.Any(o => o is AddressOf { Target: var t } && t == task)) ? null : task;
                default:
                    return null;
            }
        }
        return null;
    }

    private static bool IsAwaiter(TypeAnalysisContext type)
    {
        var definition = (type as GenericInstanceTypeAnalysisContext)?.GenericType ?? type;
        return definition is { Name: "Awaiter", DeclaringType.FullName: "Cysharp.Threading.Tasks.UniTask" or "Cysharp.Threading.Tasks.UniTask`1" };
    }

    private static bool IsTaskOf(TypeAnalysisContext? task, TypeAnalysisContext awaiter)
        => task is GenericInstanceTypeAnalysisContext t && awaiter is GenericInstanceTypeAnalysisContext a
           && t.GenericType == a.GenericType.DeclaringType && t.GenericArguments.Select(x => x.FullName).SequenceEqual(a.GenericArguments.Select(x => x.FullName));

    private static MethodAnalysisContext? GetAwaiter(TypeAnalysisContext task)
    {
        var definition = (task as GenericInstanceTypeAnalysisContext)?.GenericType ?? task;
        var method = definition.Methods.SingleOrDefault(m => m is { Name: "GetAwaiter", IsStatic: false, Parameters.Count: 0 });
        return method == null ? null
            : task is GenericInstanceTypeAnalysisContext instance ? new ConcreteGenericMethodAnalysisContext(method, instance.GenericArguments, []) : method;
    }
}
