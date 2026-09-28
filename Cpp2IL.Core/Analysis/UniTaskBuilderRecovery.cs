using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// An async UniTask method completes through its builder, whose members are inlined and read its private
/// promise and fields:
/// <code>
/// // builder.SetResult(r) / builder.SetException(e)
/// if (runnerPromise == null) result = r; else runnerPromise.SetResult(r);
/// // builder.SetResult() of a UniTask without a result
/// if (runnerPromise != null) runnerPromise.SetResult();
/// </code>
/// Call the public member on the builder field again. Runs in SSA.
/// </summary>
public static class UniTaskBuilderRecovery
{
    public static bool Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var changed = false;
        foreach (var block in graph.Blocks.ToList())
            changed |= graph.Blocks.Contains(block) && TryRecover(graph, block);
        if (changed)
            DeadCodeEliminator.Run(method);
        return changed;
    }

    private static bool TryRecover(ISILControlFlowGraph graph, Block head)
    {
        if (head.Successors.Count != 2 || head.Instructions.LastOrDefault(i => i.OpCode != OpCode.Nop) is not
                { OpCode: OpCode.ConditionalJump, Operands: [Block target, LocalVariable condition] } branch
            || head.Instructions.LastOrDefault(i => i.Destination == condition) is not
                { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, LocalVariable promise, Immediate { Value: 0 }] } test
            || InlinedListAddRecovery.StraightLine(head).LastOrDefault(i => i.Destination == promise) is not
                { OpCode: OpCode.Move, Operands: [_, FieldReference { IsStatic: false, ContainingFields: [var builderField], Field.Name: "runnerPromise" } load] }
            || !IsBuilder(builderField.FieldType))
            return false;
        var whenNull = test.OpCode == OpCode.CheckEqual ? target : head.Successors.Single(s => s != target);
        // The promise's arm can start past blocks that only jump.
        var (whenSet, passed) = UniTaskAwaiterRecovery.Through(head.Successors.Single(s => s != whenNull));
        if (whenSet == whenNull || whenSet.Predecessors is not [_])
            return false;

        // The promise's arm: runnerPromise.SetResult/SetException(value?), then on, after copies of its operands.
        var setBody = Real(whenSet).Where(i => !IsCopy(i)).ToList();
        if (setBody.FirstOrDefault() is not { OpCode: OpCode.CallVoid, Operands: { Count: 2 or 3 } operands } call
            || operands[0] is not MethodAnalysisContext { Name: "SetResult" or "SetException" } promiseMethod
            || !IsPromiseValue(Resolve(operands[1], whenSet), promise, load, InlinedListAddRecovery.StraightLine(whenSet)))
            return false;
        var arguments = call.Operands.Skip(2).Select(a => Resolve(a, whenSet)).ToList();
        if (arguments.Count > 1
            || !IsPromise(promiseMethod) || setBody.Skip(1).Any(i => i.OpCode != OpCode.Jump) || whenSet.Successors is not [var setNext])
            return false;
        // Either arm can reach the join past blocks that only jump; the last block on the way holds the edge.
        var (join, setAfter) = UniTaskAwaiterRecovery.Through(setNext);
        var setEdge = setAfter.LastOrDefault() ?? whenSet;
        List<Block> nullAfter = [];

        // The null arm stores the value into the builder's own field, or (SetResult without one) does nothing.
        Block? nullArm = null;
        if (whenNull != join)
        {
            nullArm = whenNull;
            var nullBody = Real(nullArm).Where(i => !IsCopy(i)).ToList();
            if (arguments.Count != 1 || nullArm.Predecessors is not [_] || nullArm.Successors is not [var nullNext]
                || UniTaskAwaiterRecovery.Through(nullNext) is var (nullJoin, reached) && (nullAfter = reached) is var _ && nullJoin != join
                || nullBody.FirstOrDefault() is not { OpCode: OpCode.Move, Operands: [FieldReference { ContainingFields: [var stored], Field.Name: "result" or "ex" } field, var value] }
                || stored != builderField || field.Local != load.Local || !InlinedListAddRecovery.Same(Resolve(value, nullArm), arguments[0])
                || nullBody.Skip(1).Any(i => i.OpCode != OpCode.Jump))
                return false;
        }
        else if (arguments.Count != 0)
            return false;
        var nullEdge = nullAfter.LastOrDefault() ?? nullArm ?? head;
        var setSlot = join.Predecessors.IndexOf(setEdge) + 1;
        var nullSlot = join.Predecessors.IndexOf(nullEdge) + 1;
        if (join == graph.ExitBlock || join.Instructions.Where(i => i.OpCode == OpCode.Phi)
                .Any(phi => !InlinedListAddRecovery.Same(Resolve(phi.Operands[setSlot], whenSet), Resolve(phi.Operands[nullSlot], nullArm))))
            return false;
        // Nothing else reads what the arms compute.
        var arms = passed.Append(whenSet).Concat(setAfter).Append(nullArm).Concat(nullAfter).OfType<Block>().ToHashSet();
        var armLocals = arms.SelectMany(b => b.Instructions).Select(i => i.Destination).OfType<LocalVariable>().ToHashSet();
        if (graph.Blocks.Where(b => !arms.Contains(b)).SelectMany(b => b.Instructions)
            .Any(i => i.OpCode != OpCode.Phi && DeadCodeEliminator.UsedLocals(i).Any(armLocals.Contains)))
            return false;

        var builderMethod = BuilderMember(builderField.FieldType, promiseMethod.Name, arguments.Count);
        if (builderMethod == null)
            return false;

        // builder.SetResult(value); goto join
        test.OpCode = OpCode.Nop;
        test.SetOperands();
        branch.OpCode = OpCode.CallVoid;
        branch.SetOperands([builderMethod, new AddressOf(new FieldReference(builderField, load.Local, builderField.Offset)), .. arguments]);
        branch.DeclaredArguments = 1 + arguments.Count;
        head.Instructions.Add(new Instruction(-1, OpCode.Jump, join));

        foreach (var phi in join.Instructions.Where(i => i.OpCode == OpCode.Phi))
            phi.SetOperand(setSlot, Resolve(phi.Operands[setSlot], whenSet));
        var removedEdge = join.Predecessors.IndexOf(nullEdge);
        foreach (var phi in join.Instructions.Where(i => i.OpCode == OpCode.Phi))
            phi.RemoveOperandAt(removedEdge + 1);
        join.Predecessors.RemoveAt(removedEdge);
        join.Predecessors[join.Predecessors.IndexOf(setEdge)] = head;
        foreach (var arm in arms)
        {
            arm.Successors.Clear();
            arm.Predecessors.Clear();
            graph.Blocks.Remove(arm);
        }
        head.Successors.Clear();
        head.Successors.Add(join);
        head.CalculateBlockType();
        return true;
    }

    private static bool IsCopy(Instruction instruction) => instruction is { OpCode: OpCode.Move, Operands: [LocalVariable, LocalVariable] };

    // What an operand copied inside a block holds.
    private static IOperand Resolve(IOperand operand, Block? block)
    {
        for (var steps = 0; steps < 4 && block != null && operand is LocalVariable local
                            && block.Instructions.LastOrDefault(i => i.Destination == local) is { OpCode: OpCode.Move, Operands: [_, LocalVariable source] }; steps++)
            operand = source;
        return operand;
    }

    // The tested promise, a copy of it, or the same field loaded again.
    private static bool IsPromiseValue(IOperand operand, LocalVariable promise, FieldReference load, List<Instruction> straight)
    {
        for (var steps = 0; steps < 4; steps++)
        {
            if (operand == promise)
                return true;
            if (operand is not LocalVariable local || straight.LastOrDefault(i => i.Destination == local) is not { OpCode: OpCode.Move, Operands: [_, var source] })
                return false;
            if (source is FieldReference field && field.Local == load.Local && field.Field == load.Field
                && field.ContainingFields.SequenceEqual(load.ContainingFields))
                return true;
            operand = source;
        }
        return false;
    }

    private static bool IsBuilder(TypeAnalysisContext type)
        => ((type as GenericInstanceTypeAnalysisContext)?.GenericType ?? type).FullName
            is "Cysharp.Threading.Tasks.CompilerServices.AsyncUniTaskMethodBuilder" or "Cysharp.Threading.Tasks.CompilerServices.AsyncUniTaskMethodBuilder`1";

    private static bool IsPromise(MethodAnalysisContext method)
        => ((method as ConcreteGenericMethodAnalysisContext)?.BaseMethodContext ?? method).DeclaringType?.FullName
            is "Cysharp.Threading.Tasks.CompilerServices.IStateMachineRunnerPromise" or "Cysharp.Threading.Tasks.CompilerServices.IStateMachineRunnerPromise`1";

    private static MethodAnalysisContext? BuilderMember(TypeAnalysisContext builder, string name, int parameters)
    {
        var definition = (builder as GenericInstanceTypeAnalysisContext)?.GenericType ?? builder;
        var member = definition.Methods.SingleOrDefault(m => m.Name == name && !m.IsStatic && m.Parameters.Count == parameters && m.GenericParameters.Count == 0);
        if (member == null)
            return null;
        return builder is GenericInstanceTypeAnalysisContext instance ? new ConcreteGenericMethodAnalysisContext(member, instance.GenericArguments, []) : member;
    }

    private static List<Instruction> Real(Block block) => block.Instructions.Where(i => i.OpCode != OpCode.Nop).ToList();
}
