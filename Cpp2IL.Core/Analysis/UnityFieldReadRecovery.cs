using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

public static class UnityFieldReadRecovery
{
    public static MethodAnalysisContext? TryGetGetter(FieldAnalysisContext field, MethodDefinition caller)
    {
        var owner = field.DeclaringType;
        // UGUI 1.0.0 Button.onClick directly returns m_OnClick.
        if (field.IsStatic || owner.DeclaringAssembly.Name != "UnityEngine.UI"
            || owner.FullName != "UnityEngine.UI.Button" || field.Name != "m_OnClick"
            || field.FieldType.FullName != "UnityEngine.UI.Button+ButtonClickedEvent"
            || field.FieldType.DeclaringAssembly != owner.DeclaringAssembly
            || (field.Attributes & FieldAttributes.FieldAccessMask) != FieldAttributes.Private)
            return null;

        var getter = owner.Properties.SingleOrDefault(p => p.Name == "onClick")?.Getter;
        if (getter is not { IsStatic: false, Parameters.Count: 0, GenericParameters.Count: 0 }
            || getter.Visibility != MethodAttributes.Public || getter.ReturnType != field.FieldType
            || getter.GetExtraData<MethodDefinition>("AsmResolverMethod") == caller)
            return null;

        return getter;
    }
}
