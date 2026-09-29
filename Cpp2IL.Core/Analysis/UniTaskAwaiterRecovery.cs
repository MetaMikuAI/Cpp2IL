using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// An async method awaiting a UniTask inlines the awaiter's members, which read the task's private
/// source and token:
/// <code>
/// // awaiter.IsCompleted
/// if (source != null &amp;&amp; source.GetStatus(token) == UniTaskStatus.Pending) { suspend }
/// // awaiter.GetResult()
/// r = source == null ? result : source.GetResult(token);
/// </code>
/// Native code keeps the awaiter in a stack slot or field and loads its source into a register, which
/// holds the whole awaiter's type. Call the public members on that storage again.
/// </summary>
public static class UniTaskAwaiterRecovery
{
    public static bool Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        if (!graph.Instructions.Any(i => i.IsCall && i.Operands[0] is MethodAnalysisContext { Name: "GetStatus" or "GetResult" } m && IsSource(m, m.DeclaringType?.FullName ?? "")
                                         && m.DeclaringType?.Namespace == "Cysharp.Threading.Tasks"))
            return false;
        // A status or source register only carried round a loop in phis would keep the checks alive.
        DeadCodeEliminator.RemoveDeadCopyCycles(graph);
        // Locals with a value; a register a call clobbered has none.
        var defined = graph.Instructions.Select(i => i.Destination).OfType<LocalVariable>().ToHashSet();
        defined.UnionWith(method.ParameterLocals);
        var changed = false;
        foreach (var block in graph.Blocks.ToList())
            changed |= graph.Blocks.Contains(block) && (TryIsCompleted(graph, block, defined) || TryGetResult(graph, block, defined));
        if (changed)
            DeadCodeEliminator.Run(method);
        return changed;
    }

    // head: if (a == null) goto join;  check: st = a.GetStatus(token); if (st == Pending) goto suspend; goto join
    private static bool TryIsCompleted(ISILControlFlowGraph graph, Block head, HashSet<LocalVariable> defined)
    {
        if (NullTest(head) is not var (branch, awaiter, whenNull) || head.Successors.SingleOrDefault(s => s != whenNull) is not { } entry
            || Through(entry) is not ({ Predecessors: [_] } check, var passed))
            return false;
        var body = Real(check);
        if (body is not [{ OpCode: OpCode.Call, Operands: [MethodAnalysisContext { Name: "GetStatus" } getStatus, LocalVariable status, var source, _] },
                { OpCode: OpCode.CheckEqual, Operands: [LocalVariable pending, var tested, Immediate { Value: 0 }] },
                { OpCode: OpCode.ConditionalJump, Operands: [Block suspend, var condition] }]
            || !IsSource(getStatus, "Cysharp.Threading.Tasks.IUniTaskSource") || source != awaiter.Local || tested != status || condition != pending
            || check.Successors.Count != 2 || !check.Successors.Contains(suspend) || suspend == whenNull
            || Through(check.Successors.Single(b => b != suspend)) is var (reached, rejoin) && reached != whenNull
            // The status is only seen by the check, and by the join's phis where a register carried it on.
            || graph.Blocks.Where(b => b != check).SelectMany(b => b.Instructions)
                .Any(i => (i.OpCode != OpCode.Phi || !whenNull.Instructions.Contains(i)) && DeadCodeEliminator.UsedLocals(i).Any(l => l == status || l == pending))
            || !SameFromBoth(whenNull, head, rejoin.LastOrDefault() ?? check, status, defined)
            || Member(awaiter, "get_IsCompleted") is not { } isCompleted)
            return false;

        // if (awaiter.IsCompleted) goto join; else suspend
        var completed = (LocalVariable)branch.Operands[1];
        var test = head.Instructions.Last(i => i.Destination == completed);
        test.OpCode = OpCode.Call;
        test.SetOperands(isCompleted, completed, awaiter.Receiver);
        test.DeclaredArguments = 1;
        branch.SetOperand(0, whenNull);
        Replace(graph, head, check, rejoin.LastOrDefault() ?? check, whenNull, suspend);
        foreach (var block in passed.Concat(rejoin))
            graph.Blocks.Remove(block);
        return true;
    }

    // head: if (a == null) goto whenNull (r = result);  other: r = a.GetResult(token);  both join
    private static bool TryGetResult(ISILControlFlowGraph graph, Block head, HashSet<LocalVariable> defined)
    {
        if (NullTest(head) is not var (branch, awaiter, whenNull) || head.Successors.SingleOrDefault(s => s != whenNull) is not { } entry
            || Through(entry) is not ({ Predecessors: [_] } other, var passed))
            return false;
        var body = Real(other);
        if (body.FirstOrDefault() is not { OpCode: OpCode.Call or OpCode.CallVoid } call
            || call.Operands[0] is not MethodAnalysisContext { Name: "GetResult" } getResult
            || !IsSource(getResult, call.OpCode == OpCode.Call ? "Cysharp.Threading.Tasks.IUniTaskSource`1" : "Cysharp.Threading.Tasks.IUniTaskSource")
            || call.Operands[call.OpCode == OpCode.Call ? 2 : 1] != awaiter.Local
            || body.Skip(1).Any(i => i.OpCode != OpCode.Jump)
            || other.Successors is not [var join] || join == graph.ExitBlock
            || Member(awaiter, "GetResult") is not { } memberGetResult || memberGetResult.IsVoid != (call.OpCode == OpCode.CallVoid))
            return false;
        var result = call.OpCode == OpCode.Call ? call.Operands[1] as LocalVariable : null;
        if (call.OpCode == OpCode.Call && result == null)
            return false;

        // The null-source path only computes the result it hands the join, or goes straight there.
        Block? nullPath = null;
        if (whenNull != join)
        {
            nullPath = whenNull;
            if (nullPath.Predecessors is not [_] || nullPath.Successors is not [var nullJoin] || nullJoin != join
                || Real(nullPath).Any(i => i.OpCode != OpCode.Jump && !InlinedListAddRecovery.IsArithmetic(i)
                                             && i is not { OpCode: OpCode.Move, Destination: LocalVariable }))
                return false;
        }
        var nullLocals = nullPath?.Instructions.Select(i => i.Destination).OfType<LocalVariable>().ToHashSet() ?? [];
        var callSlot = join.Predecessors.IndexOf(other) + 1;
        var nullSlot = join.Predecessors.IndexOf(nullPath ?? head) + 1;
        foreach (var phi in join.Instructions.Where(i => i.OpCode == OpCode.Phi))
        {
            // Only the result may differ between the paths, and nothing else sees the null path's values.
            if (!InlinedListAddRecovery.Same(phi.Operands[callSlot], phi.Operands[nullSlot])
                && !(phi.Operands[callSlot] == result && phi.Operands[nullSlot] is LocalVariable or Immediate)
                && !(result == null && Clobbered(phi.Operands[callSlot], defined)))
                return false;
        }
        if (graph.Blocks.Where(b => b != nullPath && b != other).SelectMany(b => b.Instructions)
            .Any(i => i.OpCode != OpCode.Phi && DeadCodeEliminator.UsedLocals(i).Any(nullLocals.Contains))
            || result != null && graph.Blocks.Where(b => b != other && b != join).SelectMany(b => b.Instructions).Any(i => DeadCodeEliminator.UsedLocals(i).Contains(result))
            || result != null && join.Instructions.Any(i => i.OpCode != OpCode.Phi && DeadCodeEliminator.UsedLocals(i).Contains(result)))
            return false;

        // r = awaiter.GetResult(); goto join
        var test = head.Instructions.Last(i => i.Destination == branch.Operands[1]);
        test.OpCode = OpCode.Nop;
        test.SetOperands();
        branch.OpCode = call.OpCode;
        branch.SetOperands(result == null ? [memberGetResult, awaiter.Receiver] : [memberGetResult, result, awaiter.Receiver]);
        branch.DeclaredArguments = 1;
        head.Instructions.Add(new Instruction(-1, OpCode.Jump, join));

        // The null path's edge (or the head's own, when it went straight to the join) goes; the call's edge,
        // carrying the result, is the head's now.
        var nullEdge = nullSlot - 1;
        foreach (var phi in join.Instructions.Where(i => i.OpCode == OpCode.Phi))
            phi.RemoveOperandAt(nullEdge + 1);
        join.Predecessors.RemoveAt(nullEdge);
        join.Predecessors[join.Predecessors.IndexOf(other)] = head;
        foreach (var arm in passed.Append(other).Append(nullPath).OfType<Block>())
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

    private readonly record struct AwaiterValue(LocalVariable Local, IOperand Receiver, TypeAnalysisContext Type);

    // The block ends in if (a == null) goto whenNull, a being an awaiter's source loaded from its storage.
    private static (Instruction Branch, AwaiterValue Awaiter, Block WhenNull)? NullTest(Block head)
    {
        if (head.Successors.Count != 2 || head.Instructions.LastOrDefault(i => i.OpCode != OpCode.Nop) is not
                { OpCode: OpCode.ConditionalJump, Operands: [Block target, LocalVariable condition] } branch
            || head.Instructions.LastOrDefault(i => i.Destination == condition) is not
                { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, LocalVariable local, Immediate { Value: 0 }] } test
            // The tested register holds the source loaded from the awaiter's storage, whatever it was typed as.
            || InlinedListAddRecovery.StraightLine(head).LastOrDefault(i => i.Destination == local) is not { OpCode: OpCode.Move, Operands: [_, var storage] }
            || StorageType(storage) is not { } type || !IsAwaiter(type)
            || Receiver(storage, type) is not { } receiver)
            return null;
        // if (a == null) goto whenNull, or if (a != null) goto on with whenNull the other way.
        var whenNull = test.OpCode == OpCode.CheckEqual ? target : head.Successors.FirstOrDefault(s => s != target);
        return whenNull == null ? null : (branch, new AwaiterValue(local, receiver, type), whenNull);
    }

    private static TypeAnalysisContext? StorageType(IOperand storage) => storage switch
    {
        LocalVariable slot => slot.Type,
        FieldReference field => field.Field.FieldType,
        _ => null,
    };

    // The awaiter's storage: a stack slot or a field of the same type, whose address the members take.
    private static IOperand? Receiver(IOperand storage, TypeAnalysisContext type) => storage switch
    {
        LocalVariable { Type: { } slotType } slot when slot.Register.Name.StartsWith("stack_") && slotType.FullName == type.FullName => new AddressOf(slot),
        FieldReference { IsStatic: false } field when field.Field.FieldType.FullName == type.FullName => new AddressOf(field),
        _ => null,
    };

    private static bool IsAwaiter(TypeAnalysisContext type)
    {
        var definition = (type as GenericInstanceTypeAnalysisContext)?.GenericType ?? type;
        return definition is { Name: "Awaiter", DeclaringType.FullName: "Cysharp.Threading.Tasks.UniTask" or "Cysharp.Threading.Tasks.UniTask`1" };
    }

    private static MethodAnalysisContext? Member(AwaiterValue awaiter, string name)
    {
        var definition = (awaiter.Type as GenericInstanceTypeAnalysisContext)?.GenericType ?? awaiter.Type;
        var member = definition.Methods.SingleOrDefault(m => m is { IsStatic: false, Parameters.Count: 0 } && m.Name == name);
        if (member == null)
            return null;
        return awaiter.Type is GenericInstanceTypeAnalysisContext instance
            ? new ConcreteGenericMethodAnalysisContext(member, instance.GenericArguments, [])
            : member;
    }

    private static bool IsSource(MethodAnalysisContext method, string interfaceName)
    {
        var definition = method is ConcreteGenericMethodAnalysisContext concrete ? concrete.BaseMethodContext : method;
        return definition.DeclaringType?.FullName == interfaceName;
    }

    // The first block from start that does more than jump on, and the jump-only blocks passed on the way.
    internal static (Block Target, List<Block> Passed) Through(Block start)
    {
        var passed = new List<Block>();
        var current = start;
        while (passed.Count < 8 && current.Predecessors is [_] && current.Successors is [var next]
               && current.Instructions.All(i => i.OpCode is OpCode.Nop or OpCode.Jump))
        {
            passed.Add(current);
            current = next;
        }
        return (current, passed);
    }

    private static List<Instruction> Real(Block block) => block.Instructions.Where(i => i.OpCode != OpCode.Nop).ToList();

    private static bool Uses(ISILControlFlowGraph graph, Block except, params LocalVariable[] locals)
        => graph.Blocks.Where(b => b != except).SelectMany(b => b.Instructions).Any(i => DeadCodeEliminator.UsedLocals(i).Any(locals.Contains));

    // The join's phis take the same value from the head as from the check, but for the check's own status.
    private static bool SameFromBoth(Block join, Block head, Block check, LocalVariable status, HashSet<LocalVariable> defined)
    {
        var fromHead = join.Predecessors.IndexOf(head) + 1;
        var fromCheck = join.Predecessors.IndexOf(check) + 1;
        return join.Instructions.Where(i => i.OpCode == OpCode.Phi)
            .All(phi => phi.Operands[fromCheck] == status || Clobbered(phi.Operands[fromCheck], defined)
                        || InlinedListAddRecovery.Same(phi.Operands[fromHead], phi.Operands[fromCheck]));
    }

    // A register version the call's clobbering made, which holds nothing the source could see.
    private static bool Clobbered(IOperand operand, HashSet<LocalVariable> defined) => operand is LocalVariable local && !defined.Contains(local);

    // The head branches to join (completed) or falls to suspend; the check block goes.
    private static void Replace(ISILControlFlowGraph graph, Block head, Block check, Block checkEdge, Block join, Block suspend)
    {
        var fromCheck = join.Predecessors.IndexOf(checkEdge);
        foreach (var phi in join.Instructions.Where(i => i.OpCode == OpCode.Phi))
            phi.RemoveOperandAt(fromCheck + 1);
        join.Predecessors.RemoveAt(fromCheck);
        suspend.Predecessors[suspend.Predecessors.IndexOf(check)] = head;
        check.Successors.Clear();
        check.Predecessors.Clear();
        graph.Blocks.Remove(check);
        head.Successors.Clear();
        head.Successors.AddRange([join, suspend]);
        head.CalculateBlockType();
    }
}
