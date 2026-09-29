using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A struct returned in registers is spilled whole, the registers stored as a pair (<c>STP X0, X1</c>), but
/// the store is modelled as writing only the first register: its first member,
/// <c>awaiter = result.tween</c>, into a location of the struct type itself. A value of type T whose first
/// member is stored into a location of type T is the whole value stored: <c>awaiter = result</c>.
/// Runs out of SSA.
/// </summary>
public static class WholeValuePieceStoreRecovery
{
    public static bool Run(MethodAnalysisContext method)
    {
        var changed = false;
        foreach (var store in method.ControlFlowGraph!.Instructions)
        {
            if (store is not { OpCode: OpCode.Move, Operands: [var target, FieldReference { IsNested: false, IsStatic: false } piece] }
                || piece.Local is not { IsThis: false, Type: { IsValueType: true } valueType } whole
                || TargetType(target) is not { } targetType || targetType.FullName != valueType.FullName
                || piece.Field.FieldType.FullName == valueType.FullName
                || FirstMember(valueType) is not { } first || first.Name != piece.Field.Name
                || target is LocalVariable local && local == whole)
                continue;
            store.SetOperands(target, whole);
            changed = true;
        }
        return changed;
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
