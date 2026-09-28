using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

public static class PrimitiveFieldReadRecovery
{
    // These primitive wrappers contain exactly the value represented by m_value.
    public static bool IsWholeValueField(FieldAnalysisContext field)
    {
        var owner = field.DeclaringType;
        return !field.IsStatic && field.Name == "m_value" && field.FieldType == owner && field.Offset == 0
            && owner.IsValueType
            && owner.FullName is "System.Int32" or "System.Int64" or "System.Single" or "System.Double" or "System.Boolean"
            && owner.DeclaringAssembly == owner.AppContext.SystemTypes.SystemObjectType.DeclaringAssembly
            && owner.DeclaringAssembly.Name == "mscorlib"
            && (field.Attributes & FieldAttributes.FieldAccessMask) == FieldAttributes.Private
            && owner.Fields.Count(f => !f.IsStatic) == 1;
    }
}
