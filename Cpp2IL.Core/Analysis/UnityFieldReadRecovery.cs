using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

public static class UnityFieldReadRecovery
{
    public static MethodAnalysisContext? TryGetComponentGetter(FieldReference reference, MethodDefinition caller)
    {
        if (reference.ContainingFields.Count != 1)
            return null;
        var container = reference.ContainingFields[0];
        var field = reference.Field;
        if (field.IsStatic || field.DeclaringType != container.FieldType
            || field.FieldType != field.AppContext.SystemTypes.SystemSingleType
            || (field.Attributes & FieldAttributes.FieldAccessMask) != FieldAttributes.Public
            || (field.DeclaringType.FullName, field.Name) is not
                (("UnityEngine.Vector2", "x" or "y")
                or ("UnityEngine.Vector3", "x" or "y" or "z")
                or ("UnityEngine.Quaternion", "x" or "y" or "z" or "w")))
            return null;
        return TryGetStaticGetter(container, caller);
    }

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

    // Public members that return exactly this private field in the official sources of the installed packages
    // (UnityEngine.CoreModule, UGUI 1.0.0, Timeline, TextMeshPro); a name ending in () is a method.
    private static string? Accessor(string assembly, string type, string field) => (assembly, type, field) switch
    {
        ("UnityEngine.UI", "UnityEngine.UI.Button", "m_OnClick") => "onClick",
        ("UnityEngine.UI", "UnityEngine.UI.ScrollRect", "m_Content") => "content",
        ("UnityEngine.UI", "UnityEngine.UI.ScrollRect", "m_Velocity") => "velocity",
        ("UnityEngine.UI", "UnityEngine.UI.RawImage", "m_Texture") => "texture",
        ("UnityEngine.UI", "UnityEngine.UI.Image", "m_Sprite") => "sprite",
        ("UnityEngine.CoreModule", "UnityEngine.Rect", "m_XMin") => "x",
        ("UnityEngine.CoreModule", "UnityEngine.Rect", "m_YMin") => "y",
        ("UnityEngine.CoreModule", "UnityEngine.Rect", "m_Width") => "width",
        ("UnityEngine.CoreModule", "UnityEngine.Rect", "m_Height") => "height",
        ("UnityEngine.CoreModule", "UnityEngine.Vector2Int" or "UnityEngine.Vector3Int", "m_X") => "x",
        ("UnityEngine.CoreModule", "UnityEngine.Vector2Int" or "UnityEngine.Vector3Int", "m_Y") => "y",
        ("UnityEngine.CoreModule", "UnityEngine.Vector3Int", "m_Z") => "z",
        ("UnityEngine.CoreModule", "UnityEngine.Ray", "m_Origin") => "origin",
        ("UnityEngine.CoreModule", "UnityEngine.Ray", "m_Direction") => "direction",
        ("UnityEngine.CoreModule", "UnityEngine.Bounds", "m_Center") => "center",
        ("UnityEngine.CoreModule", "UnityEngine.Bounds", "m_Extents") => "extents",
        ("UnityEngine.CoreModule", "UnityEngine.Playables.Playable", "m_Handle") => "GetHandle()",
        ("UnityEngine.CoreModule", "UnityEngine.Playables.FrameData", "m_FrameID") => "frameId",
        ("Unity.Timeline", "UnityEngine.Timeline.TimelineClip", "m_Asset") => "asset",
        ("Unity.Timeline", "UnityEngine.Timeline.TimelineClip", "m_Start") => "start",
        ("Unity.TextMeshPro", "TMPro.TMP_InputField", "m_OnEndEdit") => "onEndEdit",
        ("Unity.TextMeshPro", "TMPro.TMP_Dropdown", "m_OnValueChanged") => "onValueChanged",
        _ => null,
    };

    public static MethodAnalysisContext? TryGetGetter(FieldAnalysisContext field, MethodDefinition caller)
    {
        var owner = field.DeclaringType;
        if (field.IsStatic || owner.GenericParameters.Count != 0
            || (field.Attributes & FieldAttributes.FieldAccessMask) is not (FieldAttributes.Private or FieldAttributes.Assembly)
            || Accessor(owner.DeclaringAssembly.Name, owner.FullName, field.Name) is not { } name)
            return null;

        var getter = name.EndsWith("()")
            ? owner.Methods.SingleOrDefault(m => m.Name == name[..^2] && m.Parameters.Count == 0)
            : owner.Properties.SingleOrDefault(p => p.Name == name)?.Getter;
        if (getter is not { IsStatic: false, Parameters.Count: 0, GenericParameters.Count: 0 }
            || getter.Visibility != MethodAttributes.Public || getter.ReturnType != field.FieldType
            || getter.GetExtraData<MethodDefinition>("AsmResolverMethod") == caller)
            return null;

        return getter;
    }
}
