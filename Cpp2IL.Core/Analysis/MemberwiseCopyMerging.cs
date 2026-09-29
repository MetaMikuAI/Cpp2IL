using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A struct held in registers is copied into an array element or a field one member at a time from its
/// pieces: <c>array[i].source = task.source; array[i].token = task.token</c>. Those name members the
/// caller cannot access. A run of stores writing every member of one location with the same member of one
/// value, unchanged since it was read, is the whole value stored: <c>array[i] = task</c>. Runs out of SSA.
/// </summary>
public static class MemberwiseCopyMerging
{
    public static bool Run(MethodAnalysisContext method)
    {
        var changed = false;
        foreach (var block in method.ControlFlowGraph!.Blocks)
        {
            var straight = InlinedListAddRecovery.StraightLine(block);
            var offset = straight.Count - block.Instructions.Count;
            for (var i = 0; i < block.Instructions.Count; i++)
            {
                if (Piece(block.Instructions[i], straight, offset + i) is not { } first)
                    continue;
                var valueType = first.Value.Type!;
                var fields = ((valueType as GenericInstanceTypeAnalysisContext)?.GenericType ?? valueType).Fields.Where(f => !f.IsStatic).Select(f => f.Name).ToList();
                var run = new List<(Instruction Store, Copy Piece)> { (block.Instructions[i], first) };
                for (var j = i + 1; j < block.Instructions.Count && run.Count < fields.Count; j++)
                {
                    var next = block.Instructions[j];
                    // Nothing between but the next member's address.
                    if (next.OpCode == OpCode.Nop || next is { OpCode: OpCode.Move, Operands: [LocalVariable, AddressOf] })
                        continue;
                    if (Piece(next, straight, offset + j) is not { } piece || !piece.SameWhole(first))
                        break;
                    run.Add((next, piece));
                }
                if (run.Count != fields.Count || fields.Any(f => run.Count(r => r.Piece.Member.Name == f) != 1))
                    continue;

                run[0].Store.SetOperands(first.Target, first.Value);
                foreach (var (store, _) in run.Skip(1))
                {
                    store.OpCode = OpCode.Nop;
                    store.SetOperands();
                }
                changed = true;
            }
        }
        return changed;
    }

    // A store of member Member of Value into that member of Target, the whole location.
    private sealed record Copy(IOperand Target, LocalVariable Value, FieldAnalysisContext Member)
    {
        public bool SameWhole(Copy other) => Value == other.Value && Target switch
        {
            ArrayAccess a => other.Target is ArrayAccess b && a.Array == b.Array && Equals(a.Index, b.Index),
            FieldReference f => other.Target is FieldReference g && f.Local == g.Local && OverwrittenMemberStoreElimination.SameField(f.Field, g.Field)
                                && f.ContainingFields.Count == g.ContainingFields.Count
                                && f.ContainingFields.Zip(g.ContainingFields).All(p => OverwrittenMemberStoreElimination.SameField(p.First, p.Second)),
            _ => false,
        };
    }

    private static Copy? Piece(Instruction store, List<Instruction> straight, int at)
    {
        if (store is not { OpCode: OpCode.Move, Operands: [FieldReference { IsStatic: false } member, LocalVariable value] }
            || Latest(straight, at, value) is not { OpCode: OpCode.Move, Operands: [_, FieldReference { IsNested: false, IsStatic: false } read] } definition
            || read.Field.Name != member.Field.Name || read.Local.Type is not { IsValueType: true } valueType
            || member.Field.DeclaringType.FullName != valueType.FullName && member.Field.DeclaringType.FullName != ((valueType as GenericInstanceTypeAnalysisContext)?.GenericType ?? valueType).FullName
            || Written(straight, straight.IndexOf(definition), at, read.Local))
            return null;

        // The location the member belongs to: an array element reached through its address, or a field path.
        IOperand? target = member switch
        {
            { IsNested: true } => new FieldReference(member.ContainingFields[^1], member.Local, member.ContainingFields[^1].Offset)
                { ContainingFields = member.ContainingFields.Take(member.ContainingFields.Count - 1).ToList() },
            _ when Latest(straight, at, member.Local) is { OpCode: OpCode.Move, Operands: [_, AddressOf { Target: ArrayAccess element }] } address
                   && !Written(straight, straight.IndexOf(address), at, element.Array)
                   && (element.Index is not LocalVariable index || !Written(straight, straight.IndexOf(address), at, index)) => element,
            _ => null,
        };
        if (target is FieldReference whole && whole.Field.FieldType.FullName != valueType.FullName
            || target is ArrayAccess && (member.Local.Type as ByRefTypeAnalysisContext)?.ElementType.FullName != valueType.FullName)
            return null;
        return target == null ? null : new Copy(target, read.Local, member.Field);
    }

    private static Instruction? Latest(List<Instruction> straight, int at, LocalVariable local)
    {
        for (var i = at - 1; i >= 0; i--)
            if (straight[i].Destination == local)
                return straight[i];
        return null;
    }

    // The value is written between its member read and the store: directly, or by a call when its address is taken.
    private static bool Written(List<Instruction> straight, int from, int to, LocalVariable value)
        => from < 0 || straight.Skip(from + 1).Take(to - from - 1).Any(i => i.Destination == value
            || i.IsCall && Addressed(straight, value) || i.Operands.Any(o => o is AddressOf { Target: var t } && t == value));

    private static bool Addressed(List<Instruction> straight, LocalVariable value)
        => value.Register.Name.StartsWith("stack_") || straight.Any(i => i.Operands.Any(o => o is AddressOf { Target: var t } && t == value));
}
