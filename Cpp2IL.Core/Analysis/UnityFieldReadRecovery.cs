using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

public static class UnityFieldReadRecovery
{
    public static MethodAnalysisContext? TryGetStaticGetter(FieldAnalysisContext field, MethodDefinition caller)
    {
        var owner = field.DeclaringType;
        if (!field.IsStatic || owner.DeclaringAssembly.Name != "UnityEngine.CoreModule"
            || field.FieldType != owner || !owner.IsValueType
            || (field.Attributes & FieldAttributes.FieldAccessMask) != FieldAttributes.Private
            || (field.Attributes & FieldAttributes.InitOnly) == 0)
            return null;

        var property = (owner.FullName, field.Name) switch
        {
            ("UnityEngine.Vector2" or "UnityEngine.Vector3", "zeroVector") => "zero",
            ("UnityEngine.Vector2" or "UnityEngine.Vector3", "oneVector") => "one",
            ("UnityEngine.Vector2" or "UnityEngine.Vector3", "upVector") => "up",
            ("UnityEngine.Vector2" or "UnityEngine.Vector3", "downVector") => "down",
            ("UnityEngine.Vector2" or "UnityEngine.Vector3", "leftVector") => "left",
            ("UnityEngine.Vector2" or "UnityEngine.Vector3", "rightVector") => "right",
            ("UnityEngine.Vector3", "forwardVector") => "forward",
            ("UnityEngine.Vector3", "backVector") => "back",
            ("UnityEngine.Quaternion", "identityQuaternion") => "identity",
            _ => null,
        };
        var getter = owner.Properties.SingleOrDefault(p => p.Name == property)?.Getter;
        if (property == null || getter is not { IsStatic: true, Parameters.Count: 0, GenericParameters.Count: 0 }
            || getter.Visibility != MethodAttributes.Public || getter.ReturnType != owner
            || getter.GetExtraData<MethodDefinition>("AsmResolverMethod") == caller)
            return null;

        return getter;
    }

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
