using System.Linq;
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
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction is { OpCode: OpCode.Move, Operands: [var target, FieldReference piece] }
                && TargetType(target) is { } targetType && Whole(piece, targetType) is { } whole
                && !(target is LocalVariable local && local == whole))
            {
                instruction.SetOperands(target, whole);
                changed = true;
                continue;
            }

            // A struct argument: the parameter's type names what the registers hold.
            if (instruction is not { OpCode: OpCode.Call or OpCode.CallVoid } || instruction.Operands[0] is not MethodAnalysisContext callee)
                continue;
            var first = (instruction.OpCode == OpCode.Call ? 2 : 1) + (callee.IsStatic ? 0 : 1);
            for (var i = first; i < instruction.Operands.Count && i - first < callee.Parameters.Count; i++)
            {
                if (instruction.Operands[i] is FieldReference argument
                    && Whole(argument, callee.Parameters[i - first].ParameterType) is { } wholeArgument)
                {
                    instruction.SetOperand(i, wholeArgument);
                    changed = true;
                }
            }
        }
        return changed;
    }

    // The whole value a first-member read reads from, when that value has the expected struct type.
    private static IOperand? Whole(FieldReference piece, TypeAnalysisContext expected)
    {
        if (piece.IsStatic || piece.Field.FieldType.FullName == expected.FullName)
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
        return wholeType is { IsValueType: true } && wholeType.FullName == expected.FullName
               && FirstMember(wholeType) is { } firstMember && firstMember.Name == piece.Field.Name
            ? whole : null;
    }

    private static TypeAnalysisContext? TargetType(IOperand target) => target switch
    {
        LocalVariable { IsThis: false } local => local.Type,
        FieldReference field => field.Field.FieldType,
        _ => null,
    };

    // The member at offset 0: the first instance field, of a struct with more than one.
    private static FieldAnalysisContext? FirstMember(TypeAnalysisContext type)
    {
        var definition = (type as GenericInstanceTypeAnalysisContext)?.GenericType ?? type;
        if (definition.IsEnumType)
            return null;
        var fields = definition.Fields.Where(f => !f.IsStatic).ToList();
        return fields.Count > 1 ? fields[0] : null;
    }
}
