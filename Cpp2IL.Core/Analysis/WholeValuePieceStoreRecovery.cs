using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A struct held in registers moves whole, all its registers at once: spilled as a pair
/// (<c>STP X0, X1</c>) or passed in consecutive argument registers. Only the first register is modelled,
/// so the value moved is its first member: <c>awaiter = result.tween</c>, <c>SetColor(color.r)</c>, where
/// the location or parameter has the struct type itself. A value of type T whose first member goes where a T
/// is expected is the whole value: <c>awaiter = result</c>, <c>SetColor(color)</c>. Runs out of SSA.
/// </summary>
public static class WholeValuePieceStoreRecovery
{
    public static bool Run(MethodAnalysisContext method)
    {
        var changed = false;
        var instructions = method.ControlFlowGraph!.Instructions;
        var definitions = instructions.Where(i => i.Destination is LocalVariable).GroupBy(i => (LocalVariable)i.Destination!)
            .ToDictionary(g => g.Key, g => g.ToList());
        var uses = instructions.SelectMany(i => DeadCodeEliminator.UsedLocals(i)).GroupBy(l => l).ToDictionary(g => g.Key, g => g.Count());
        foreach (var block in method.ControlFlowGraph.Blocks)
        foreach (var instruction in block.Instructions)
        {
            if (instruction is { OpCode: OpCode.Move, Operands: [var target, FieldReference piece] }
                && TargetType(target) is { } targetType && Whole(piece, targetType) is { } whole
                && !(target is LocalVariable local && local == whole))
            {
                instruction.SetOperands(target, whole);
                changed = true;
                continue;
            }
            // The first member copied to a local only to be stored here: tween = result.tween; awaiter = tween.
            if (instruction is { OpCode: OpCode.Move, Operands: [var copyTarget, LocalVariable stored] }
                && TargetType(copyTarget) is { IsValueType: true } copyTargetType && CopiedWhole(stored, copyTargetType, block, instruction) is { } storedWhole
                && !(copyTarget is LocalVariable same && same == storedWhole))
            {
                instruction.SetOperands(copyTarget, storedWhole);
                changed = true;
                continue;
            }

            // A struct returned in registers: the return type names what they hold.
            if (instruction is { OpCode: OpCode.Return, Operands: [FieldReference returned] }
                && method.ReturnType is { IsValueType: true } returnType && Whole(returned, returnType) is { } wholeReturned)
            {
                instruction.SetOperands(wholeReturned);
                changed = true;
                continue;
            }

            // A struct argument: the parameter's type names what the registers hold.
            if (instruction is not { OpCode: OpCode.Call or OpCode.CallVoid } || instruction.Operands[0] is not MethodAnalysisContext callee)
                continue;
            var first = (instruction.OpCode == OpCode.Call ? 2 : 1) + (callee.IsStatic ? 0 : 1);
            for (var i = first; i < instruction.Operands.Count && i - first < callee.Parameters.Count; i++)
            {
                var parameterType = callee.Parameters[i - first].ParameterType;
                if (instruction.Operands[i] is FieldReference argument && Whole(argument, parameterType) is { } wholeArgument)
                {
                    instruction.SetOperand(i, wholeArgument);
                    changed = true;
                }
                // The first member copied to a local only to be passed here: float r = color.r; ... SetColor(r).
                else if (instruction.Operands[i] is LocalVariable copy
                         && CopiedWhole(copy, parameterType, block, instruction) is { } copiedWhole)
                {
                    instruction.SetOperand(i, copiedWhole);
                    changed = true;
                }
            }
        }
        return changed;

        // The whole value behind a local holding only its first member, copied once and read only here.
        IOperand? CopiedWhole(LocalVariable copy, TypeAnalysisContext expected, Block block, Instruction user)
            => uses.GetValueOrDefault(copy) == 1
               && definitions.GetValueOrDefault(copy) is [{ OpCode: OpCode.Move, Operands: [_, FieldReference copied] } definition]
               && Whole(copied, expected) is { } copiedWhole && Unchanged(block, definition, user, copied)
                ? copiedWhole : null;
    }

    // The copy and the call on one straight line, with nothing between that may write the value copied from:
    // a struct local is written only directly or through its address, anything else by any call or store.
    private static bool Unchanged(Block block, Instruction definition, Instruction call, FieldReference copied)
    {
        var straight = InlinedListAddRecovery.StraightLine(block);
        var from = straight.IndexOf(definition);
        var to = straight.IndexOf(call);
        if (from < 0 || to < from)
            return false;
        var between = straight.Skip(from + 1).Take(to - from - 1);
        var root = copied.Local;
        if (!copied.IsStatic && root is { IsThis: false, Type.IsValueType: true } && root.Register.Name?.StartsWith("stack_") != true)
            return !between.Any(i => i.Destination == root || i.Destination is FieldReference f && f.Local == root
                                     || i.Operands.Any(o => o is AddressOf { Target: var t } && t == root));
        return !between.Any(i => i.IsCall || i.Destination is FieldReference or MemoryOperand or ArrayAccess);
    }

    // The whole value a first-member read reads from, when that value has the expected struct type.
    private static IOperand? Whole(FieldReference piece, TypeAnalysisContext expected)
    {
        if (piece.IsStatic && !piece.IsNested || piece.Field.FieldType.FullName == expected.FullName)
            return null;
        IOperand whole;
        TypeAnalysisContext? wholeType;
        if (piece.IsNested)
        {
            var parent = new FieldReference(piece.ContainingFields[^1], piece.Local, piece.ContainingFields[^1].Offset)
                { ContainingFields = piece.ContainingFields.Take(piece.ContainingFields.Count - 1).ToList() };
            whole = parent;
            wholeType = parent.Field.FieldType;
        }
        else
        {
            if (piece.Local.IsThis)
                return null;
            whole = piece.Local;
            wholeType = piece.Local.Type;
        }
        if (wholeType is not { IsValueType: true } || FirstMember(wholeType) is not { } firstMember || firstMember.Name != piece.Field.Name)
            return null;
        if (wholeType.FullName == expected.FullName)
            return whole;
        // The first member of a first member: playable.m_Handle.m_Handle is still the playable.
        return whole is FieldReference outer ? Whole(outer, expected) : null;
    }

    private static TypeAnalysisContext? TargetType(IOperand target) => target switch
    {
        LocalVariable { IsThis: false } local => local.Type,
        FieldReference field => field.Field.FieldType,
        _ => null,
    };

    // The member at offset 0: the first instance field of a struct.
    private static FieldAnalysisContext? FirstMember(TypeAnalysisContext type)
    {
        var definition = (type as GenericInstanceTypeAnalysisContext)?.GenericType ?? type;
        if (definition.IsEnumType)
            return null;
        var fields = definition.Fields.Where(f => !f.IsStatic).ToList();
        return fields.Count > 0 ? fields[0] : null;
    }
}
