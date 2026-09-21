using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.ISIL;

public class FieldReference(FieldAnalysisContext field, LocalVariable local, int offset,
    FieldAnalysisContext? containingField = null) : IOperand
{
    public FieldAnalysisContext Field = field;
    public LocalVariable Local = local;
    public int Offset = offset;
    public IReadOnlyList<FieldAnalysisContext> ContainingFields = containingField == null ? [] : [containingField];
    public FieldAnalysisContext? ContainingField
    {
        get => ContainingFields.FirstOrDefault();
        set => ContainingFields = value == null ? [] : [value];
    }

    public bool IsNested => ContainingFields.Count != 0;

    public override string ToString() => IsNested
        ? $"{Local.Name}.{string.Join('.', ContainingFields.Select(f => f.Name).Append(Field.Name))} ({Field.FieldType.FullName})"
        : $"{Local.Name}.{Field.Name} ({Field.FieldType.FullName})";
}
