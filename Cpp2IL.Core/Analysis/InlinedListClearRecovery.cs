using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Analysis.InlinedListAddRecovery;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// The native compiler inlines <c>List&lt;T&gt;.Clear</c>, leaving its private members in the caller:
/// <code>
/// int size = list._size;
/// list._size = 0;
/// list._version++;
/// if (size &gt; 0) Array.Clear(list._items, 0, size);
/// </code>
/// where the <c>Array.Clear</c> is only there when <c>T</c> holds references. Emit <c>list.Clear()</c>
/// again. Runs in SSA, alongside <see cref="InlinedListAddRecovery"/>.
/// </summary>
public static class InlinedListClearRecovery
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

    private static bool TryRecover(ISILControlFlowGraph graph, Block block)
    {
        var sizeStore = block.Instructions.FirstOrDefault(i => i is { OpCode: OpCode.Move, Operands: [FieldReference { Field.Name: "_size" }, Immediate { Value: 0 }] });
        if (sizeStore?.Operands[0] is not FieldReference { Local: var list } sizeField || !IsListField(sizeField, list, "_size")
            || Clear(sizeField) is not { } clear)
            return false;

        // The straight-line code ending in this block.
        var straight = StraightLine(block);

        // list._version = list._version + 1, next to the size store.
        var versionStore = straight.FirstOrDefault(i => i is { OpCode: OpCode.Move, Operands: [FieldReference f, LocalVariable v] }
                                                        && IsListField(f, list, "_version") && IsVersionIncrement(straight, v, list));
        if (versionStore == null)
            return false;
        var (first, last) = straight.IndexOf(versionStore) < straight.IndexOf(sizeStore) ? (versionStore, sizeStore) : (sizeStore, versionStore);

        var element = ((GenericInstanceTypeAnalysisContext)((ConcreteGenericFieldAnalysisContext)sizeField.Field).DeclaringType).GenericArguments[0];
        var branch = block.Instructions.LastOrDefault(i => i.OpCode != OpCode.Nop);
        if (branch is { OpCode: OpCode.ConditionalJump, Operands: [Block target, LocalVariable condition] } && block.Successors.Count == 2
            // if (size > 0) Array.Clear(list._items, 0, size), before the continuation both arms share.
            && ClearsItems(graph, block, straight, list, target, condition, out var arm, out var skip)
            // The call goes at the branch: nothing from the stores on sees the list's state change.
            && Unobserved(straight.Skip(straight.IndexOf(first)), sizeStore, versionStore, branch))
        {
            sizeStore.OpCode = OpCode.Nop;
            sizeStore.SetOperands();
            versionStore.OpCode = OpCode.Nop;
            versionStore.SetOperands();
            branch.OpCode = OpCode.CallVoid;
            branch.SetOperands(clear, list);
            branch.DeclaredArguments = 1;
            block.Instructions.Add(new Instruction(-1, OpCode.Jump, skip));

            foreach (var successor in arm.Successors)
            {
                var index = successor.Predecessors.IndexOf(arm);
                foreach (var phi in successor.Instructions.Where(i => i.OpCode == OpCode.Phi))
                    phi.RemoveOperandAt(index + 1);
                successor.Predecessors.RemoveAt(index);
            }
            arm.Successors.Clear();
            arm.Predecessors.Clear();
            graph.Blocks.Remove(arm);
            block.Successors.Clear();
            block.Successors.Add(skip);
            block.CalculateBlockType();
            return true;
        }

        // A T without references has no Array.Clear: the stores are the whole of it, and the call goes at the first.
        var between = straight.Skip(straight.IndexOf(first)).Take(straight.IndexOf(last) - straight.IndexOf(first) + 1);
        if (!element.IsValueType || !Unobserved(between, sizeStore, versionStore, null))
            return false;
        versionStore.OpCode = OpCode.Nop;
        versionStore.SetOperands();
        sizeStore.OpCode = OpCode.CallVoid;
        sizeStore.SetOperands(clear, list);
        sizeStore.DeclaredArguments = 1;
        if (straight.IndexOf(versionStore) < straight.IndexOf(sizeStore))
        {
            // Keep the call where the first store was.
            var (callBlock, storeBlock) = (graph.FindBlockByInstruction(sizeStore)!, graph.FindBlockByInstruction(versionStore)!);
            callBlock.Instructions[callBlock.Instructions.IndexOf(sizeStore)] = versionStore;
            storeBlock.Instructions[storeBlock.Instructions.IndexOf(versionStore)] = sizeStore;
        }
        return true;
    }

    private static bool Unobserved(IEnumerable<Instruction> instructions, Instruction sizeStore, Instruction versionStore, Instruction? branch)
        => instructions.All(i => i == sizeStore || i == versionStore || i == branch || i.OpCode is OpCode.Nop or OpCode.Jump
                                 || IsArithmetic(i) || i.OpCode is >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual);

    // The branch skips to the continuation unless size > 0, where the arm clears items[0..size) first.
    private static bool ClearsItems(ISILControlFlowGraph graph, Block block, List<Instruction> straight, LocalVariable list,
        Block target, LocalVariable condition, out Block arm, out Block skip)
    {
        arm = skip = null!;
        if (Definition(straight, condition) is not { Operands: [_, LocalVariable size, Immediate { Value: var bound }, ..] } comparison
            || !Loads(straight, size, list, "_size"))
            return false;
        bool? jumpsWhenEmpty = (comparison.OpCode, bound) switch
        {
            (OpCode.CheckLess, 1) or (OpCode.CheckLessOrEqual, 0) or (OpCode.CheckEqual, 0) => true,
            (OpCode.CheckGreaterOrEqual, 1) or (OpCode.CheckGreater, 0) or (OpCode.CheckNotEqual, 0) => false,
            _ => null,
        };
        if (jumpsWhenEmpty == null)
            return false;
        var clearing = arm = block.Successors.Single(s => (s == target) != jumpsWhenEmpty);
        skip = block.Successors.Single(s => s != clearing);
        if (arm == skip || arm.Predecessors is not [_])
            return false;

        // The arm may load the items itself.
        bool LoadsItems(Instruction i) => i is { OpCode: OpCode.Move, Operands: [LocalVariable, FieldReference f] } && IsListField(f, list, "_items");
        var body = arm.Instructions.Where(i => i.OpCode != OpCode.Nop && !IsArithmetic(i) && !LoadsItems(i)).ToList();
        if (body.FirstOrDefault() is not { OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: "Clear" } clearMethod, var items, Immediate { Value: 0 }, var count] }
            || clearMethod.DeclaringType?.FullName != "System.Array" || !Same(count, size)
            || !(items is FieldReference f && IsListField(f, list, "_items")
                 || items is LocalVariable loaded && Loads(straight.Concat(arm.Instructions).ToList(), loaded, list, "_items")))
            return false;

        // Nothing past the arm reads its values.
        var armLocals = arm.Instructions.Select(i => i.Destination).OfType<LocalVariable>().ToHashSet();
        if (graph.Blocks.Where(b => b != clearing).SelectMany(b => b.Instructions).Any(i => DeadCodeEliminator.UsedLocals(i).Any(armLocals.Contains)))
            return false;

        var rest = body.Skip(1).ToList();
        // To the skipped-to block, whose phis take the same value from the arm as from the branch.
        if (arm.Successors is [var next] && next == skip && rest.All(i => i.OpCode == OpCode.Jump))
        {
            var armIndex = skip.Predecessors.IndexOf(arm) + 1;
            var blockIndex = skip.Predecessors.IndexOf(block) + 1;
            return skip.Instructions.Where(i => i.OpCode == OpCode.Phi).All(phi => Same(phi.Operands[armIndex], phi.Operands[blockIndex]));
        }
        // Or both return the same value.
        var skipBody = skip.Instructions.Where(i => i.OpCode != OpCode.Nop && !IsArithmetic(i)).ToList();
        return rest is [{ OpCode: OpCode.Return } armReturn] && skipBody is [{ OpCode: OpCode.Return } skipReturn]
               && armReturn.Operands.Count == skipReturn.Operands.Count
               && armReturn.Operands.Zip(skipReturn.Operands).All(p => Same(p.First, p.Second))
               && arm.Successors.SequenceEqual(skip.Successors) && skip.Predecessors is [_];
    }

    private static bool IsVersionIncrement(List<Instruction> straight, LocalVariable value, LocalVariable list)
        => Definition(straight, value) is { OpCode: OpCode.Add, Operands: [_, var old, Immediate { Value: 1 }] }
           && (old is FieldReference f && IsListField(f, list, "_version")
               || old is LocalVariable loaded && Loads(straight, loaded, list, "_version"));

    private static MethodAnalysisContext? Clear(FieldReference size)
    {
        if (size.Field is not ConcreteGenericFieldAnalysisContext { BaseFieldContext.DeclaringType: var definition, DeclaringType: GenericInstanceTypeAnalysisContext instance })
            return null;
        var clear = definition.Methods.SingleOrDefault(m => m is { Name: "Clear", IsStatic: false, Parameters.Count: 0, GenericParameters.Count: 0 });
        return clear == null ? null : new ConcreteGenericMethodAnalysisContext(clear, instance.GenericArguments, []);
    }
}
