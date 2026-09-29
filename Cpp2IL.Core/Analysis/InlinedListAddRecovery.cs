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
        if (!graph.Blocks.Any(b => SlowCall(b) != null))
            return false;
        // Registers the slow arm loads its argument into merge at the join in phis, often only feeding each
        // other round a loop; those would keep the arms apart.
        DeadCodeEliminator.RemoveDeadCopyCycles(graph);
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
        var straight = StraightLine(head);

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
        // The length can still be in a local of its own here, even as the raw max_length load.
        if (length is LocalVariable lengthLocal)
            length = Definition(straight, lengthLocal) switch
            {
                { OpCode: OpCode.Move, Operands: [_, ArrayLength loaded] } => loaded,
                { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: LocalVariable array, Index: null } raw] }
                    when raw.Addend == 3L * resize.AppContext.Binary.PointerSizeBytes => new ArrayLength(array),
                _ => length,
            };
        if (size is not LocalVariable sizeLocal || length is not ArrayLength { Array: var items }
            || target != (jumpsWhenFull ? slow : fast)
            || !Loads(graph, straight, sizeLocal, list, "_size") || !Loads(graph, straight, items, list, "_items"))
            return false;

        // list._version = list._version + 1, on the way to the branch.
        var versionStore = straight.LastOrDefault(i => i is { OpCode: OpCode.Move, Operands: [FieldReference f, LocalVariable] }
                                                                   && IsListField(f, list, "_version"));
        if (versionStore == null || Definition(straight, (LocalVariable)versionStore.Operands[1]) is not
                { OpCode: OpCode.Add, Operands: [_, LocalVariable oldVersion, Immediate { Value: 1 }] }
            || !Loads(graph, straight, oldVersion, list, "_version"))
            return false;

        // The fast arm: size + 1 into list._size, the item into items[size].
        var body = fast.Instructions.Where(i => i.OpCode != OpCode.Nop).ToList();
        var increment = body.FirstOrDefault(i => i is { OpCode: OpCode.Add, Operands: [LocalVariable, var s, Immediate { Value: 1 }] } && s == sizeLocal);
        var sizeStore = body.FirstOrDefault(i => i is { OpCode: OpCode.Move, Operands: [FieldReference f, var v] }
                                                 && IsListField(f, list, "_size") && v == increment?.Destination);
        var elementStore = body.FirstOrDefault(i => i is { OpCode: OpCode.Move, Operands: [ArrayAccess a, var v] }
                                                    && a.Array == items && a.Index == sizeLocal && Same(v, item))
                           ?? body.FirstOrDefault(i => i is { OpCode: OpCode.Move, Operands: [MemoryOperand m, var v] }
                                                       && Same(v, item) && IsElementAddress(straight.Concat(fast.Instructions).ToList(), m, items, sizeLocal, resize));
        if (increment == null || sizeStore == null)
            return false;
        // A struct item is written member by member: into items[size], or into the argument AddWithResize takes.
        List<Instruction> fastWrites = elementStore == null ? [] : [elementStore], slowBuild = [];
        if (elementStore == null && !StructItem(graph, straight, body, slow, call, items, sizeLocal, item, resize, out fastWrites, out slowBuild))
            return false;
        // Nothing past the arms reads their values, such as the incremented size or the element's address.
        var armLocals = fast.Instructions.Concat(slow.Instructions).Select(i => i.Destination).OfType<LocalVariable>().ToHashSet();
        if (graph.Blocks.Where(b => b != fast && b != slow).SelectMany(b => b.Instructions)
            .Any(i => DeadCodeEliminator.UsedLocals(i).Any(armLocals.Contains)))
            return false;
        var fastRest = body.Except([increment, sizeStore, .. fastWrites]).Where(i => !IsArithmetic(i)).ToList();
        var slowRest = slow.Instructions.Where(i => i.OpCode != OpCode.Nop && i != call && !IsArithmetic(i)).Except(slowBuild).ToList();

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
        head.Instructions.InsertRange(head.Instructions.IndexOf(branch), slowBuild);
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

    // The code on the only way into a block: its single predecessors back to a join, past checks that otherwise throw.
    internal static List<Instruction> StraightLine(Block block)
    {
        var straight = new List<Instruction>(block.Instructions);
        for (var current = block; current.Predecessors is [var previous] && previous != block && straight.Count < 512
             && previous.Successors.All(s => s == current || Throws(s));)
        {
            straight.InsertRange(0, previous.Instructions);
            current = previous;
        }
        return straight;
    }

    private static bool Throws(Block block) => block.Instructions.LastOrDefault(i => i.OpCode != OpCode.Nop) is { OpCode: OpCode.Throw }
                                               || block.Successors is [var only] && only.Instructions.LastOrDefault(i => i.OpCode != OpCode.Nop) is { OpCode: OpCode.Throw };

    // items[size].m = v for each member m, through &items[size], and item.m = v alike before AddWithResize(item).
    private static bool StructItem(ISILControlFlowGraph graph, List<Instruction> straight, List<Instruction> body, Block slow, Instruction call,
        LocalVariable items, LocalVariable size, IOperand item, MethodAnalysisContext resize, out List<Instruction> fastWrites, out List<Instruction> slowBuild)
    {
        fastWrites = slowBuild = [];
        if (item is not LocalVariable built || resize is not ConcreteGenericMethodAnalysisContext { TypeGenericParameters: [var element] }
            || element is not { IsValueType: true, IsEnumType: false } || element is GenericInstanceTypeAnalysisContext)
            return false;
        var fields = element.Fields.Where(f => !f.IsStatic).ToList();
        var visible = straight.Concat(body).ToList();
        bool IsElementAddress(LocalVariable local) => Definition(visible, local) is
            { OpCode: OpCode.Move, Operands: [_, AddressOf { Target: ArrayAccess access }] } && access.Array == items && access.Index == size;

        var fastStores = body.Where(i => i is { OpCode: OpCode.Move, Operands: [FieldReference { IsNested: false, Local: var e }, _] } && IsElementAddress(e)).ToList();
        var slowStores = slow.Instructions.Where(i => i is { OpCode: OpCode.Move, Operands: [FieldReference { IsNested: false, Local: var l }, _] } && l == built).ToList();
        var fastByField = fastStores.GroupBy(i => ((FieldReference)i.Operands[0]).Field).ToDictionary(g => g.Key, g => g.ToList());
        var slowByField = slowStores.GroupBy(i => ((FieldReference)i.Operands[0]).Field).ToDictionary(g => g.Key, g => g.ToList());
        if (fields.Count == 0 || fastByField.Count != fields.Count || slowByField.Count != fields.Count
            || fields.Any(f => !fastByField.TryGetValue(f, out var fastStore) || fastStore.Count != 1 || !slowByField.TryGetValue(f, out var slowStore)
                               || slowStore.Count != 1 || !Same(fastStore[0].Operands[1], slowStore[0].Operands[1])))
            return false;

        // The built argument is only this: its stores and the call.
        var own = slowStores.Append(call).ToHashSet();
        if (graph.Instructions.Any(i => !own.Contains(i) && (DeadCodeEliminator.UsedLocals(i).Contains(built) || i.Destination == built)))
            return false;

        var addresses = body.Where(i => i.Destination is LocalVariable local && IsElementAddress(local));
        fastWrites = fastStores.Concat(addresses).ToList();
        slowBuild = slowStores;
        return true;
    }

    // Not yet recovered as items[size]: [items + (size << log2(element size)) + array header], at the element's width.
    private static bool IsElementAddress(List<Instruction> instructions, MemoryOperand memory, LocalVariable items, LocalVariable size, MethodAnalysisContext resize)
    {
        if (memory is not { Base: LocalVariable address, Index: null } || resize is not ConcreteGenericMethodAnalysisContext { TypeGenericParameters: [var element] })
            return false;
        var pointerSize = element.AppContext.Binary.PointerSizeBytes;
        var width = element.IsValueType ? Utils.TypeSizes.UnboxedSize(element, pointerSize) : pointerSize;
        if (width is not (1 or 2 or 4 or 8) || memory.AccessSize != 0 && memory.AccessSize != width)
            return false;

        // Walk the constant additions down to items + scaled size.
        var offset = memory.Addend;
        for (var steps = 0; steps < 4 && Definition(instructions, address) is { OpCode: OpCode.Add, Operands: [_, LocalVariable inner, Immediate constant] }; steps++)
        {
            offset += constant.Value;
            address = inner;
        }
        if (offset != 4L * pointerSize || Definition(instructions, address) is not { OpCode: OpCode.Add, Operands: [_, var left, var right] })
            return false;
        var scaled = left == items ? right : right == items ? left : null;
        return width == 1 ? scaled == size
            : scaled is LocalVariable shifted && Definition(instructions, shifted) is { OpCode: OpCode.ShiftLeft, Operands: [_, var index, Immediate shift] }
              && index == size && 1L << (int)shift.Value == width;
    }

    // The arm's first real instruction, after any member stores building its argument: list.AddWithResize(item).
    private static Instruction? SlowCall(Block block)
    {
        var body = block.Instructions.Where(i => i.OpCode != OpCode.Nop).ToList();
        var index = body.FindIndex(i => i.OpCode != OpCode.Move || i.Operands[0] is not FieldReference { IsNested: false });
        return index >= 0 && body[index] is { OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: "AddWithResize" } m, LocalVariable, var item] } call
               && IsList(Base(m).DeclaringType)
               && body.Take(index).All(i => ((FieldReference)i.Operands[0]).Local == item) ? call : null;
    }

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

    // As above, or a phi of such loads: the paths into a join each read the field, nothing after the read
    // on its path (a call) able to change it before the join.
    private static bool Loads(ISILControlFlowGraph graph, List<Instruction> instructions, LocalVariable local, LocalVariable list, string field)
    {
        if (Loads(instructions, local, list, field))
            return true;
        if (Definition(instructions, local) is not { OpCode: OpCode.Phi } phi
            || graph.Blocks.FirstOrDefault(b => b.Instructions.Contains(phi)) is not { } join
            || phi.Operands.Count != join.Predecessors.Count + 1)
            return false;
        for (var i = 1; i < phi.Operands.Count; i++)
        {
            var path = join.Predecessors[i - 1].Instructions;
            if (phi.Operands[i] is not LocalVariable incoming
                || path.LastOrDefault(x => x.Destination == incoming) is not { OpCode: OpCode.Move, Operands: [_, FieldReference f] } read
                || !IsListField(f, list, field)
                || path.Skip(path.IndexOf(read) + 1).Any(x => x.IsCall))
                return false;
        }
        return true;
    }

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
