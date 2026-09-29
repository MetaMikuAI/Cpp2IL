using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A struct held in registers is copied one member at a time from its pieces:
/// <c>array[i].source = task.source; array[i].token = task.token</c>, or a getter's
/// <c>result.x = this.position.x; result.y = this.position.y; ...</c>. Those name members the caller
/// cannot access. A run of stores writing every member of one location with the same member of one value,
/// unchanged since it was read, is the whole value stored: <c>array[i] = task</c>, <c>result = this.position</c>.
/// The location is a field, an array element or a struct local; the value a struct local or a field.
/// Runs out of SSA.
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
                var fields = ((first.Type as GenericInstanceTypeAnalysisContext)?.GenericType ?? first.Type).Fields.Where(f => !f.IsStatic).Select(f => f.Name).ToList();
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

    // A store of member Member of Value into that member of Target, both whole locations of the struct Type.
    private sealed record Copy(IOperand Target, IOperand Value, FieldAnalysisContext Member, TypeAnalysisContext Type)
    {
        public bool SameWhole(Copy other) => Same(Value, other.Value) && Same(Target, other.Target);
    }

    private static bool Same(IOperand left, IOperand right) => left switch
    {
        LocalVariable l => l == right,
        ArrayAccess a => right is ArrayAccess b && a.Array == b.Array && Equals(a.Index, b.Index),
        FieldReference f => right is FieldReference g && f.Local == g.Local && OverwrittenMemberStoreElimination.SameField(f.Field, g.Field)
                            && f.ContainingFields.Count == g.ContainingFields.Count
                            && f.ContainingFields.Zip(g.ContainingFields).All(p => OverwrittenMemberStoreElimination.SameField(p.First, p.Second)),
        _ => false,
    };

    private static Copy? Piece(Instruction store, List<Instruction> straight, int at)
    {
        if (store is not { OpCode: OpCode.Move, Operands: [FieldReference { IsStatic: false } member, LocalVariable value] }
            || Latest(straight, at, value) is not { OpCode: OpCode.Move, Operands: [_, FieldReference { IsStatic: false } read] } definition
            || read.Field.Name != member.Field.Name
            || Whole(read) is not ({ } source, { } valueType)
            || member.Field.DeclaringType.FullName != valueType.FullName && member.Field.DeclaringType.FullName != ((valueType as GenericInstanceTypeAnalysisContext)?.GenericType ?? valueType).FullName
            || Changed(straight, straight.IndexOf(definition), at, source))
            return null;

        // The location the member belongs to: a field path, an array element reached through its address, or a struct local.
        IOperand? target = member switch
        {
            { IsNested: true } => Parent(member),
            _ when Latest(straight, at, member.Local) is { OpCode: OpCode.Move, Operands: [_, AddressOf { Target: ArrayAccess element }] } address
                   && !Changed(straight, straight.IndexOf(address), at, element.Array)
                   && (element.Index is not LocalVariable index || !Changed(straight, straight.IndexOf(address), at, index)) => element,
            // A struct's own this stays assigned member by member, which its constructor requires.
            { Local: { IsThis: false, Type: { IsValueType: true } localType } } when localType.FullName == valueType.FullName => member.Local,
            _ => null,
        };
        if (target is FieldReference whole && whole.Field.FieldType.FullName != valueType.FullName
            || target is ArrayAccess && (member.Local.Type as ByRefTypeAnalysisContext)?.ElementType.FullName != valueType.FullName
            || target != null && Same(target, source))
            return null;
        return target == null ? null : new Copy(target, source, member.Field, valueType);
    }

    // The whole struct a member read reads from: a local, or the field path above it.
    private static (IOperand, TypeAnalysisContext)? Whole(FieldReference read)
    {
        if (!read.IsNested)
            return read.Local.Type is { IsValueType: true } type ? (read.Local, type) : null;
        var parent = Parent(read);
        return parent.Field.FieldType is { IsValueType: true } fieldType ? (parent, fieldType) : null;
    }

    private static FieldReference Parent(FieldReference member) => new(member.ContainingFields[^1], member.Local, member.ContainingFields[^1].Offset)
        { ContainingFields = member.ContainingFields.Take(member.ContainingFields.Count - 1).ToList() };

    private static Instruction? Latest(List<Instruction> straight, int at, LocalVariable local)
    {
        for (var i = at - 1; i >= 0; i--)
            if (straight[i].Destination == local)
                return straight[i];
        return null;
    }

    // The value may have changed between its member read and the store.
    private static bool Changed(List<Instruction> straight, int from, int to, IOperand value)
    {
        if (from < 0)
            return true;
        var between = straight.Skip(from + 1).Take(to - from - 1);
        return value switch
        {
            // A local: written directly, or by a call when its address is taken.
            LocalVariable local => between.Any(i => i.Destination == local || i.IsCall && Addressed(straight, local)
                || i.Operands.Any(o => o is AddressOf { Target: var t } && t == local)),
            // A field: a call or a store that may reach it.
            FieldReference field => between.Any(i => i.IsCall || i.Destination is MemoryOperand or ArrayAccess
                || i.Destination is FieldReference stored && MayAlias(stored, field)),
            _ => true,
        };
    }

    // A store into a struct local cannot reach anything else; one into the same object reaches the field only
    // along the same path.
    private static bool MayAlias(FieldReference stored, FieldReference field)
    {
        if (stored.Local.Type is { IsValueType: true } && stored.Local != field.Local)
            return false;
        if (stored.Local != field.Local)
            return true;
        var storedPath = stored.ContainingFields.Append(stored.Field).ToList();
        var fieldPath = field.ContainingFields.Append(field.Field).ToList();
        return storedPath.Zip(fieldPath).All(p => OverwrittenMemberStoreElimination.SameField(p.First, p.Second));
    }

    private static bool Addressed(List<Instruction> straight, LocalVariable value)
        => value.Register.Name.StartsWith("stack_") || straight.Any(i => i.Operands.Any(o => o is AddressOf { Target: var t } && t == value));
}
