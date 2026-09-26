using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Recovers IL unbox.any from il2cpp's inlined UnBox: <c>obj->klass->element_class == T->element_class</c>,
/// else throw InvalidCastException, then <c>il2cpp_vm_object_unbox(obj)</c> and a load of the payload.
/// The value type is taken only from a comparison that dominates the call: the element-class check above,
/// or an exact class test the compiler merged it into (<c>obj->klass == T</c> implies the element classes match).
/// </summary>
internal static class UnboxRecovery
{
    // Il2CppClass::element_class in the 64-bit v29-v31 layout.
    private const long ElementClassOffset = 0x40;

    private sealed record Guard(TypeAnalysisContext Type, SsaFacts.EqualityBranch Branch, Block Checked, bool ComparesElementClass);

    internal static bool Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not { } graph)
            return false;
        var calls = graph.Blocks.SelectMany(b => b.Instructions.Where(IsUnbox).Select(i => (Block: b, Call: i))).ToList();
        if (calls.Count == 0)
            return false;

        var elementClassLayout = method.AppContext.Binary.PointerSizeBytes == 8 && method.AppContext.MetadataVersion is >= 29 and < 32;
        var facts = new SsaFacts(graph);
        var dominators = new DominatorInfo(graph);
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var changed = false;
        var pruned = false;
        foreach (var (block, call) in calls)
        {
            var pointer = (LocalVariable)call.Operands[1];
            var boxed = call.Operands[2];
            // The unboxed pointer must only be read once, as the whole value.
            if (facts.UsesOf(pointer) is not [{ OpCode: OpCode.Move, Operands: [LocalVariable value,
                    MemoryOperand { Base: LocalVariable loaded, Index: null, Addend: 0, AccessSize: var size }] } load]
                || loaded != pointer
                || FindGuard(block, facts.Root(boxed), facts, dominators, elementClassLayout) is not { } guard)
                continue;
            var type = guard.Type;
            if (!type.IsValueType || type is GenericParameterTypeAnalysisContext || IsNullable(type)
                || TypeSizes.UnboxedSize(type, pointerSize) != size
                || value.Type != null && value.Type != type && !SameEnumStorage(type, value.Type))
                continue;

            value.Type ??= type;
            call.OpCode = OpCode.Unbox;
            call.SetOperands(value, type, boxed);
            load.OpCode = OpCode.Nop;
            load.SetOperands();
            changed = true;

            // unbox.any performs the element-class check itself, so its InvalidCastException branch
            // can go when nothing observable happens between that branch and the unbox.
            if (guard.ComparesElementClass && SsaFacts.Throws(guard.Branch.WhenDifferent, "InvalidCastException")
                && facts.OnlyBranchReads(guard.Branch) && NothingObservableBefore(guard.Checked, call))
            {
                SsaFacts.NeverTake(guard.Branch, guard.Branch.WhenDifferent);
                pruned = true;
            }
        }
        if (pruned)
            ConstantBranchFolder.PruneSsa(graph);
        return changed;
    }

    private static bool IsUnbox(Instruction instruction) => instruction is
    {
        OpCode: OpCode.Call,
        Operands: [StringLiteral { Value: nameof(BaseKeyFunctionAddresses.il2cpp_vm_object_unbox) or nameof(BaseKeyFunctionAddresses.il2cpp_object_unbox) },
            LocalVariable, _, ..]
    };

    // An enum is held as its underlying integer, so a local typed as that integer, or as another enum
    // over it (such as a shared-generic placeholder), stores the unboxed value unchanged.
    private static bool SameEnumStorage(TypeAnalysisContext type, TypeAnalysisContext local)
        => type.IsEnumType && type.EnumUnderlyingType is { } underlying
           && (local == underlying || local.IsEnumType && local.EnumUnderlyingType == underlying);

    private static bool IsNullable(TypeAnalysisContext type)
        => type is GenericInstanceTypeAnalysisContext { GenericType: { Namespace: "System", Name: "Nullable`1" } };

    // Walk up the dominator tree for a block entered only when the object's class matched a constant.
    private static Guard? FindGuard(Block block, IOperand boxed, SsaFacts facts, DominatorInfo dominators, bool elementClassLayout)
    {
        for (var current = block; current != null; current = dominators.ImmediateDominators.GetValueOrDefault(current))
        {
            if (current.Predecessors is not [var test] || facts.EqualityBranchOf(test) is not { } branch)
                continue;
            if (branch.WhenEqual == current && (Compared(branch.Left, branch.Right) ?? Compared(branch.Right, branch.Left)) is { } found)
                return new Guard(found.Type, branch, current, found.ElementClass);
            // An isinst of a value type recovered earlier holds only for a boxed value of exactly that type.
            var tested = branch.Right is Immediate { Value: 0 } ? branch.Left : branch.Left is Immediate { Value: 0 } ? branch.Right : null;
            if (branch.WhenDifferent == current && tested != null
                && facts.Definition(tested) is { OpCode: OpCode.IsInstance, Operands: [_, TypeAnalysisContext instanceType, var instance] }
                && Equals(facts.Root(instance), boxed))
                return new Guard(instanceType, branch, current, false);
        }
        return null;

        (TypeAnalysisContext Type, bool ElementClass)? Compared(IOperand objectSide, IOperand classSide)
        {
            if (facts.LoadBase(objectSide, 0) is { } instance && Equals(instance, boxed)
                && SsaFacts.ClassConstant(facts.Root(classSide)) is { } exact)
                return (exact, false);
            if (elementClassLayout && facts.LoadBase(objectSide, ElementClassOffset) is { } klass
                && facts.LoadBase(klass, 0) is { } owner && Equals(owner, boxed)
                && facts.LoadBase(classSide, ElementClassOffset) is { } expected && SsaFacts.ClassConstant(expected) is { } type)
                return (type, true);
            return null;
        }
    }

    // Only local computations may run between the check and the unbox, so dropping the check cannot
    // move an exception past a side effect.
    private static bool NothingObservableBefore(Block start, Instruction call)
    {
        var visited = new HashSet<Block>();
        for (var block = start; visited.Add(block); block = block.Successors[0])
        {
            foreach (var instruction in block.Instructions)
            {
                if (instruction == call)
                    return true;
                if (instruction.OpCode is OpCode.Nop or OpCode.Jump)
                    continue;
                if (instruction.Destination is not LocalVariable
                    || instruction.OpCode is not (OpCode.Move or OpCode.Add or OpCode.Subtract or OpCode.ShiftLeft
                        or (>= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual))
                    || instruction.Operands.Skip(1).Any(o => o is MemoryOperand or FieldReference or ArrayAccess))
                    return false;
            }
            if (block.Successors is not [var next] || next.Predecessors.Count != 1)
                return false;
        }
        return false;
    }
}
