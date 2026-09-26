using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Removes the covariance check il2cpp emits before a reference is stored into an array,
/// <c>if (value != null &amp;&amp; IsInst(value, array->klass->element_class) == null) throw new ArrayTypeMismatchException()</c>,
/// once the store it guards is proven to follow. IL's stelem performs exactly that check itself.
/// </summary>
internal static class ArrayStoreCheckRecovery
{
    // Il2CppClass::element_class in the 64-bit v29-v31 layout, and the first element of an Il2CppArray.
    private const long ElementClassOffset = 0x40;
    private const long FirstElementOffset = 0x20;
    private const long ElementSize = 8;

    internal static bool Run(MethodAnalysisContext method)
    {
        if (method.AppContext.Binary.PointerSizeBytes != 8 || method.AppContext.MetadataVersion is < 29 or >= 32
            || method.ControlFlowGraph is not { } graph || !graph.Instructions.Any(IsTypeCheck))
            return false;

        var facts = new SsaFacts(graph);
        var removed = graph.Blocks.ToList().Select(block => TryRemove(block, facts)).OfType<Removed>().ToList();
        if (removed.Count == 0)
            return false;
        // Checks of stores into one array can share its element class, and merges can carry the
        // registers they loaded, so fold the null tests only once whatever read those is gone.
        DeadCodeEliminator.Run(graph);
        facts = new SsaFacts(graph);
        foreach (var check in removed)
            FoldNullTest(check.Block, check.Value, check.Store, facts);
        ConstantBranchFolder.PruneSsa(graph);
        return true;
    }

    private sealed record Removed(Block Block, IOperand Value, Block Store);

    private static bool IsTypeCheck(Instruction instruction) => instruction is
    {
        OpCode: OpCode.Call,
        Operands: [StringLiteral { Value: nameof(BaseKeyFunctionAddresses.il2cpp_vm_object_is_inst) }, LocalVariable, _, _, ..]
    };

    private static Removed? TryRemove(Block block, SsaFacts facts)
    {
        if (facts.EqualityBranchOf(block) is not { } check || !facts.OnlyBranchReads(check))
            return null;
        var result = (check.Left, check.Right) switch
        {
            (LocalVariable local, Immediate { Value: 0 }) => local,
            (Immediate { Value: 0 }, LocalVariable local) => local,
            _ => null
        };
        // The branch taken when IsInst returns null must be the ArrayTypeMismatchException throw.
        if (result == null || facts.UsesOf(result) is not [var comparison] || comparison != check.Comparison
            || facts.DefiningInstruction(result) is not { } call || !IsTypeCheck(call)
            || !SsaFacts.Throws(check.WhenEqual, "ArrayTypeMismatchException"))
            return null;

        var value = facts.Root(call.Operands[2]);
        if (facts.LoadBase(call.Operands[3], ElementClassOffset) is not { } klass
            || facts.LoadBase(klass, 0) is not LocalVariable array
            || !StoreFollows(check.WhenDifferent, array, value, facts))
            return null;

        call.OpCode = OpCode.Nop;
        call.SetOperands();
        SsaFacts.NeverTake(check, check.WhenEqual);
        return new Removed(block, value, check.WhenDifferent);
    }

    // The type check runs only for a non-null value. When the null test skips to where the checked
    // path rejoins it and that path computes nothing else, the test belongs to the check.
    private static void FoldNullTest(Block block, IOperand value, Block pass, SsaFacts facts)
    {
        var chain = new HashSet<Block> { block };
        var entry = block;
        while (entry.Predecessors is [var only] && only.Successors.Count == 1 && chain.Add(only))
            entry = only;
        if (entry.Predecessors is not [var test] || chain.Contains(test) || facts.EqualityBranchOf(test) is not { } nullTest
            || !facts.OnlyBranchReads(nullTest) || nullTest.WhenDifferent != entry
            || !((Equals(facts.Root(nullTest.Left), value) && nullTest.Right is Immediate { Value: 0 })
                 || (Equals(facts.Root(nullTest.Right), value) && nullTest.Left is Immediate { Value: 0 })))
            return;
        // Blocks only this path runs may sit between the check and the join.
        var last = block;
        for (var next = pass; next != nullTest.WhenEqual; last = next, next = next.Successors[0])
            if (next.Successors.Count != 1 || next.Predecessors.Count != 1 || !chain.Add(next))
                return;
        // A null value then takes the checked path, so the join must merge the same values from both.
        var join = nullTest.WhenEqual;
        var viaTest = join.Predecessors.IndexOf(test);
        var viaCheck = join.Predecessors.IndexOf(last);
        if (viaTest < 0 || viaCheck < 0 || join.Instructions.Any(i => i.OpCode == OpCode.Phi
                && (i.Operands.Count != join.Predecessors.Count + 1
                    || !Equals(facts.Root(i.Operands[viaTest + 1]), facts.Root(i.Operands[viaCheck + 1])))))
            return;
        foreach (var instruction in chain.SelectMany(b => b.Instructions))
        {
            if (instruction.OpCode is OpCode.Nop or OpCode.Jump || instruction == block.Instructions[^1])
                continue;
            if (instruction.OpCode is not (OpCode.Move or OpCode.Not or (>= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual))
                || instruction.Destination is not LocalVariable local
                || facts.UsesOf(local).Any(u => u.OpCode != OpCode.Nop && !chain.Any(b => b.Instructions.Contains(u))))
                return;
        }
        SsaFacts.NeverTake(nullTest, entry);
    }

    // The checked value must be the next thing stored, and into an element of the checked array.
    private static bool StoreFollows(Block start, LocalVariable array, IOperand value, SsaFacts facts)
    {
        var visited = new HashSet<Block>();
        for (var block = start; visited.Add(block); block = block.Successors[0])
        {
            foreach (var instruction in block.Instructions)
            {
                if (instruction.OpCode is OpCode.Nop or OpCode.Phi or OpCode.Jump)
                    continue;
                if (instruction is { OpCode: OpCode.Move, Operands: [MemoryOperand destination, var stored] })
                    return Equals(facts.Root(stored), value) && ElementAddress(destination.Base, array, facts, 0) is { } element
                        && (element.Indexed || destination.Index != null
                            || (element.Displacement + destination.Addend - FirstElementOffset) is >= 0 and var offset && offset % ElementSize == 0);
                // Anything else must be a pure local computation, such as the element address.
                if (instruction.Destination is not LocalVariable || instruction.OpCode is not (OpCode.Move or OpCode.Add
                        or OpCode.Subtract or OpCode.ShiftLeft or OpCode.ShiftRight or OpCode.Multiply or OpCode.ZeroExtend
                        or OpCode.SignExtend or OpCode.ConvertNumeric))
                    return false;
            }
            if (block.Successors.Count != 1)
                return false;
        }
        return false;
    }

    // An address built from the array by adding constants and, possibly, a variable element offset
    // (an index, or a strength-reduced loop offset). Only a purely constant one can be checked here.
    private static (long Displacement, bool Indexed)? ElementAddress(IOperand? address, LocalVariable array, SsaFacts facts, int depth)
    {
        if (address == null)
            return null;
        var root = facts.Root(address);
        if (root == array)
            return (0, false);
        if (depth > 4 || facts.Definition(root) is not { OpCode: OpCode.Add, Operands: [_, var left, var right] })
            return null;
        if (right is Immediate displacement)
            return ElementAddress(left, array, facts, depth + 1) is { } inner ? (inner.Displacement + displacement.Value, inner.Indexed) : null;
        if (left is Immediate leading)
            return ElementAddress(right, array, facts, depth + 1) is { } inner ? (inner.Displacement + leading.Value, inner.Indexed) : null;
        return (ElementAddress(left, array, facts, depth + 1) ?? ElementAddress(right, array, facts, depth + 1)) is { } based
            ? (based.Displacement, true) : null;
    }
}
