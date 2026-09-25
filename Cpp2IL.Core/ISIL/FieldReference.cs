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

    /// <summary>
    /// Width in bytes of the native memory access this reference was resolved from, or 0 when unknown.
    /// A store can resolve to a whole embedded value type while covering only part of it (one native
    /// store spanning two of its members), so this is what proves a store writes the entire value.
    /// </summary>
    public int AccessSize;
    public IReadOnlyList<FieldAnalysisContext> ContainingFields = containingField == null ? [] : [containingField];
    public FieldAnalysisContext? ContainingField
    {
        get => ContainingFields.FirstOrDefault();
        set => ContainingFields = value == null ? [] : [value];
    }

    public bool IsNested => ContainingFields.Count != 0;

    /// <summary>
    /// Whether the access is rooted at static storage, e.g. <c>Vector3.oneVector.y</c>, where the
    /// accessed member itself is an instance field of the static value type. Such an access does not
    /// read <see cref="Local"/>, which only locates the static storage it was resolved from.
    /// </summary>
    public bool IsStatic => (IsNested ? ContainingFields[0] : Field).IsStatic;

    public override string ToString() => IsNested
        ? $"{Local.Name}.{string.Join('.', ContainingFields.Select(f => f.Name).Append(Field.Name))} ({Field.FieldType.FullName})"
        : $"{Local.Name}.{Field.Name} ({Field.FieldType.FullName})";
}
