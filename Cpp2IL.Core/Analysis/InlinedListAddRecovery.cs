using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// The native compiler inlines <c>List&lt;T&gt;.Add</c>, leaving its private members in the caller:
/// <code>
/// list._version++;
/// if ((uint)size &lt; (uint)items.Length) { list._size = size + 1; items[size] = item; }
/// else list.AddWithResize(item);
/// </code>
/// where <c>size</c> and <c>items</c> are <c>list._size</c> and <c>list._items</c>. Both arms continue
/// alike, so the whole shape is the public call <c>list.Add(item)</c> again. Runs in SSA, where every
/// read of the arms' values is visible; the loads feeding the branch die with it.
/// </summary>
public static class InlinedListAddRecovery
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
        if (head.Successors.Count != 2 || head.Instructions.LastOrDefault() is not
                { OpCode: OpCode.ConditionalJump, Operands: [Block target, LocalVariable condition] } branch)
            return false;

        var slow = head.Successors.FirstOrDefault(s => SlowCall(s) != null);
        var fast = head.Successors.FirstOrDefault(s => s != slow);
        if (slow == null || fast == null || slow.Predecessors is not [_] || fast.Predecessors is not [_])
            return false;
        var call = SlowCall(slow)!;
        if (call.Operands is not [MethodAnalysisContext resize, LocalVariable list, var item] || call.DeclaredArguments is not (0 or 2))
            return false;

        // The straight-line code ending in the branch; lowering leaves block boundaries inside it.
        var straight = new List<Instruction>(head.Instructions);
        for (var current = head; current.Predecessors is [var previous] && previous.Successors is [_] && previous != head && straight.Count < 512;)
        {
            straight.InsertRange(0, previous.Instructions);
            current = previous;
        }

        // The capacity test: jumps to the slow arm when size >= items.Length.
        var definition = Definition(straight, condition);
        // An unsigned comparison carries its operand type last.
        if (definition?.Operands is not { Count: 3 or 4 } operands || operands.Count == 4 && operands[3] is not TypeAnalysisContext)
            return false;
        var (left, right) = (operands[1], operands[2]);
        var (size, length, jumpsWhenFull) = definition.OpCode switch
        {
            OpCode.CheckGreaterOrEqual => (left, right, true),
            OpCode.CheckLess => (left, right, false),
            OpCode.CheckLessOrEqual => (right, left, true),
            OpCode.CheckGreater => (right, left, false),
            _ => (null, null, false),
        };
        // The length can still be in a local of its own here.
        if (length is LocalVariable lengthLocal && Definition(straight, lengthLocal) is { OpCode: OpCode.Move, Operands: [_, ArrayLength loaded] })
            length = loaded;
        if (size is not LocalVariable sizeLocal || length is not ArrayLength { Array: var items }
            || target != (jumpsWhenFull ? slow : fast)
            || !Loads(straight, sizeLocal, list, "_size") || !Loads(straight, items, list, "_items"))
            return false;

        // list._version = list._version + 1, on the way to the branch.
        var versionStore = straight.LastOrDefault(i => i is { OpCode: OpCode.Move, Operands: [FieldReference f, LocalVariable] }
                                                                   && IsListField(f, list, "_version"));
        if (versionStore == null || Definition(straight, (LocalVariable)versionStore.Operands[1]) is not
                { OpCode: OpCode.Add, Operands: [_, LocalVariable oldVersion, Immediate { Value: 1 }] }
            || !Loads(straight, oldVersion, list, "_version"))
            return false;

        // The fast arm: size + 1 into list._size, the item into items[size].
        var body = fast.Instructions.Where(i => i.OpCode != OpCode.Nop).ToList();
        var increment = body.FirstOrDefault(i => i is { OpCode: OpCode.Add, Operands: [LocalVariable, var s, Immediate { Value: 1 }] } && s == sizeLocal);
        var sizeStore = body.FirstOrDefault(i => i is { OpCode: OpCode.Move, Operands: [FieldReference f, var v] }
                                                 && IsListField(f, list, "_size") && v == increment?.Destination);
        var elementStore = body.FirstOrDefault(i => i is { OpCode: OpCode.Move, Operands: [ArrayAccess a, var v] }
                                                    && a.Array == items && a.Index == sizeLocal && Same(v, item));
        if (increment == null || sizeStore == null || elementStore == null)
            return false;
        // Nothing past the arms reads their values, such as the incremented size or the element's address.
        var armLocals = fast.Instructions.Concat(slow.Instructions).Select(i => i.Destination).OfType<LocalVariable>().ToHashSet();
        if (graph.Blocks.Where(b => b != fast && b != slow).SelectMany(b => b.Instructions)
            .Any(i => DeadCodeEliminator.UsedLocals(i).Any(armLocals.Contains)))
            return false;
        var fastRest = body.Except([increment, sizeStore, elementStore]).Where(i => !IsArithmetic(i)).ToList();
        var slowRest = slow.Instructions.Where(i => i.OpCode != OpCode.Nop && i != call && !IsArithmetic(i)).ToList();

        // Both arms continue alike: to one block, or by returning the same value.
        Instruction continuation;
        if (fast.Successors is [var join] && slow.Successors is [var slowJoin] && join == slowJoin && join != graph.ExitBlock
            && fastRest.All(i => i.OpCode == OpCode.Jump) && slowRest.All(i => i.OpCode == OpCode.Jump))
            continuation = new Instruction(-1, OpCode.Jump, join);
        else if (fastRest is [{ OpCode: OpCode.Return } fastReturn] && slowRest is [{ OpCode: OpCode.Return } slowReturn]
                 && fastReturn.Operands.Count == slowReturn.Operands.Count
                 && fastReturn.Operands.Zip(slowReturn.Operands).All(p => Same(p.First, p.Second))
                 && fast.Successors.SequenceEqual(slow.Successors))
            continuation = new Instruction(-1, OpCode.Return, fastReturn.Operands.ToList());
        else
            return false;

        // A join's phis, as at a loop header, take the same value from either arm.
        var next = fast.Successors.ToList();
        if (next.Any(s => s.Instructions.Any(i => i.OpCode == OpCode.Phi
                && !Same(i.Operands[s.Predecessors.IndexOf(fast) + 1], i.Operands[s.Predecessors.IndexOf(slow) + 1]))))
            return false;

        var add = Add(resize);
        if (add == null)
            return false;

        versionStore.OpCode = OpCode.Nop;
        versionStore.SetOperands();
        branch.OpCode = OpCode.CallVoid;
        branch.SetOperands(add, list, item);
        branch.DeclaredArguments = 2;
        branch.NativeAddress = call.NativeAddress;
        head.Instructions.Add(continuation);

        // The head takes the fast arm's place at the join; the slow arm's edge goes.
        foreach (var successor in next)
        {
            successor.Predecessors[successor.Predecessors.IndexOf(fast)] = head;
            var slowIndex = successor.Predecessors.IndexOf(slow);
            foreach (var phi in successor.Instructions.Where(i => i.OpCode == OpCode.Phi))
                phi.RemoveOperandAt(slowIndex + 1);
            successor.Predecessors.RemoveAt(slowIndex);
        }
        foreach (var arm in new[] { fast, slow })
        {
            arm.Successors.Clear();
            arm.Predecessors.Clear();
            graph.Blocks.Remove(arm);
        }
        head.Successors.Clear();
        head.Successors.AddRange(next);
        head.CalculateBlockType();
        return true;
    }

    // The arm's first real instruction: list.AddWithResize(item).
    private static Instruction? SlowCall(Block block)
        => block.Instructions.FirstOrDefault(i => i.OpCode != OpCode.Nop) is
            { OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: "AddWithResize" } m, LocalVariable, _] } call
           && IsList(Base(m).DeclaringType) ? call : null;

    private static MethodAnalysisContext? Add(MethodAnalysisContext resize)
    {
        if (resize is not ConcreteGenericMethodAnalysisContext { BaseMethodContext: var definition } concrete)
            return null;
        var add = definition.DeclaringType?.Methods.SingleOrDefault(m => m is { Name: "Add", IsStatic: false, Parameters.Count: 1, GenericParameters.Count: 0 });
        return add == null ? null : new ConcreteGenericMethodAnalysisContext(add, concrete.TypeGenericParameters, []);
    }

    // Register arithmetic left over from the inlined body, such as the element's address.
    internal static bool IsArithmetic(Instruction instruction)
        => instruction is { OpCode: OpCode.Move or OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.ShiftLeft
               or OpCode.ShiftRight or OpCode.ConvertNumeric or OpCode.ZeroExtend or OpCode.SignExtend, Destination: LocalVariable }
           && instruction.Operands.Skip(1).All(o => o is LocalVariable or Immediate);

    internal static Instruction? Definition(List<Instruction> instructions, LocalVariable local) => instructions.LastOrDefault(i => i.Destination == local);

    internal static bool Loads(List<Instruction> instructions, LocalVariable local, LocalVariable list, string field)
        => Definition(instructions, local) is { OpCode: OpCode.Move, Operands: [_, FieldReference f] } && IsListField(f, list, field);

    internal static bool IsListField(FieldReference reference, LocalVariable list, string name)
    {
        if (reference.IsNested || reference.Local != list)
            return false;
        var field = reference.Field is ConcreteGenericFieldAnalysisContext { BaseFieldContext: var definition } ? definition : reference.Field;
        return field.Name == name && IsList(field.DeclaringType);
    }

    private static MethodAnalysisContext Base(MethodAnalysisContext method)
        => method is ConcreteGenericMethodAnalysisContext { BaseMethodContext: var definition } ? definition : method;

    private static bool IsList(TypeAnalysisContext? type)
        => type is { FullName: "System.Collections.Generic.List`1" }
           && type.DeclaringAssembly == type.AppContext.SystemTypes.SystemObjectType.DeclaringAssembly;

    internal static bool Same(IOperand left, IOperand right) => ReferenceEquals(left, right)
        || left is Immediate l && right is Immediate r && Equals(l.Value, r.Value);
}
