using System.Linq;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.ISIL;

public class FieldReference(FieldAnalysisContext field, LocalVariable local, int offset) : IOperand
{
    public FieldAnalysisContext Field = field;
    public LocalVariable Local = local;
    public int Offset = offset;

    /// <summary>
    /// Subsequent fields for nested value-type access (e.g. saveFile.storagePartial.playerData:
    /// Field = storagePartial, NestedFields = [playerData]). Empty for a plain field access.
    /// </summary>
    public FieldAnalysisContext[] NestedFields = [];

    /// <summary>
    /// Type of the value this reference reads or writes: the leaf field's type when nested.
    /// </summary>
    public TypeAnalysisContext LeafType => NestedFields.Length > 0 ? NestedFields[^1].FieldType : Field.FieldType;

    public override string ToString() => NestedFields.Length > 0
        ? $"{Local.Name}.{Field.Name}.{string.Join(".", NestedFields.Select(f => f.Name))} ({LeafType.FullName})"
        : $"{Local.Name}.{Field.Name} ({Field.FieldType.FullName})";
}
