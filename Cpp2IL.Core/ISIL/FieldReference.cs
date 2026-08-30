using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.ISIL;

public class FieldReference(FieldAnalysisContext field, LocalVariable local, int offset,
    FieldAnalysisContext? containingField = null) : IOperand
{
    public FieldAnalysisContext Field = field;
    public LocalVariable Local = local;
    public int Offset = offset;
    public FieldAnalysisContext? ContainingField = containingField;

    public bool IsNested => ContainingField != null;

    public override string ToString() => IsNested
        ? $"{Local.Name}.{ContainingField!.Name}.{Field.Name} ({Field.FieldType.FullName})"
        : $"{Local.Name}.{Field.Name} ({Field.FieldType.FullName})";
}
