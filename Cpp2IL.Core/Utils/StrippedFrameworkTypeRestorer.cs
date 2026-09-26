using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils;

/// <summary>
/// Metadata keeps some information only as flags that decompilers write back as pseudo-custom attributes:
/// type layout (<c>[StructLayout]</c>), method implementation flags (<c>[MethodImpl]</c>) and the assembly
/// version (<c>[assembly: AssemblyVersion]</c>). The runtime never needs those attribute types, so the linker
/// strips them from the corlib. When the metadata carries such flags and the corlib lost the type, the type
/// is restored in the corlib with its framework namespace, name and public surface.
///
/// The linker likewise strips the getter of an attribute's auto-property that is only ever set as a named
/// argument. A named argument needs a read-write property, so such a getter is restored when the backing
/// field proves the property is an auto-property.
///
/// Constants are inlined at compile time, so the linker strips the unused ones, but a decompiler writes a
/// floating-point literal that is a simple fraction or multiple of pi or e as <c>Math.PI</c> or
/// <c>Math.E</c> without checking the corlib still declares them. Those two are restored with their
/// framework values.
/// </summary>
public static class StrippedFrameworkTypeRestorer
{
    private const MethodAttributes Constructor = MethodAttributes.Public | MethodAttributes.HideBySig
        | MethodAttributes.SpecialName | MethodAttributes.RTSpecialName;

    private const MethodAttributes Accessor = MethodAttributes.Public | MethodAttributes.HideBySig | MethodAttributes.SpecialName;

    public static void Restore(ApplicationAnalysisContext appContext)
    {
        var corlib = appContext.SystemTypes.SystemObjectType.DeclaringAssembly;
        var metadataTypes = appContext.AllTypes.Where(t => t.Definition != null).ToList();

        if (metadataTypes.Any(HasNonDefaultLayout))
            RestoreStructLayout(appContext, corlib);

        if (metadataTypes.SelectMany(t => t.Methods).Any(m => m.Definition != null && HasMethodImplOptions(m.ImplAttributes)))
            RestoreMethodImpl(appContext, corlib);

        RestoreAssemblyVersion(appContext, corlib);
        RestoreMathConstants(appContext, corlib);

        foreach (var type in metadataTypes.Where(IsAttributeType))
            RestoreAutoPropertyGetters(type);
    }

    // A decompiler writes [StructLayout] when a type's layout differs from its C# default, or it has a
    // packing size or class size: sequential for structs, auto for classes. Enums and interfaces have none.
    internal static bool HasNonDefaultLayout(TypeAnalysisContext type)
    {
        if (type.IsInterface || type.IsEnumType) return false;
        var layout = type.Attributes & TypeAttributes.LayoutMask;
        if (!type.IsValueType) return layout != TypeAttributes.AutoLayout;
        return layout != TypeAttributes.SequentialLayout
            || type.Definition is { PackingSizeIsDefault: false } or { ClassSizeIsDefault: false };
    }

    // Everything but the code type and PreserveSig (which has its own attribute) becomes [MethodImpl].
    internal static bool HasMethodImplOptions(MethodImplAttributes attributes)
        => (attributes & ~(MethodImplAttributes.CodeTypeMask | MethodImplAttributes.PreserveSig)) != 0;

    private static void RestoreStructLayout(ApplicationAnalysisContext appContext, AssemblyAnalysisContext corlib)
    {
        const string ns = "System.Runtime.InteropServices";
        if (corlib.GetTypeByFullName($"{ns}.StructLayoutAttribute") != null) return;
        var types = appContext.SystemTypes;

        var layoutKind = corlib.GetTypeByFullName($"{ns}.LayoutKind")
            ?? InjectEnum(appContext, corlib, ns, "LayoutKind", ("Sequential", 0), ("Explicit", 2), ("Auto", 3));

        var attribute = corlib.InjectType(ns, "StructLayoutAttribute", types.SystemAttributeType,
            TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.BeforeFieldInit);
        InjectConstructor(attribute, [layoutKind], ["layoutKind"]);
        InjectConstructor(attribute, [types.SystemInt16Type], ["layoutKind"]);
        attribute.InjectFieldContext("Pack", types.SystemInt32Type, FieldAttributes.Public);
        attribute.InjectFieldContext("Size", types.SystemInt32Type, FieldAttributes.Public);
        if (corlib.GetTypeByFullName($"{ns}.CharSet") is { } charSet)
            attribute.InjectFieldContext("CharSet", charSet, FieldAttributes.Public);
        InjectGetOnlyProperty(attribute, "Value", layoutKind);
    }

    private static void RestoreMethodImpl(ApplicationAnalysisContext appContext, AssemblyAnalysisContext corlib)
    {
        const string ns = "System.Runtime.CompilerServices";
        if (corlib.GetTypeByFullName($"{ns}.MethodImplAttribute") != null) return;
        var types = appContext.SystemTypes;

        // The values are those of System.Reflection.MethodImplAttributes.
        var options = corlib.GetTypeByFullName($"{ns}.MethodImplOptions")
            ?? InjectEnum(appContext, corlib, ns, "MethodImplOptions", ("Unmanaged", 0x4), ("NoInlining", 0x8),
                ("ForwardRef", 0x10), ("Synchronized", 0x20), ("NoOptimization", 0x40), ("PreserveSig", 0x80),
                ("AggressiveInlining", 0x100), ("InternalCall", 0x1000));

        var attribute = corlib.InjectType(ns, "MethodImplAttribute", types.SystemAttributeType,
            TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.BeforeFieldInit);
        InjectConstructor(attribute, [options], ["methodImplOptions"]);
        InjectConstructor(attribute, [types.SystemInt16Type], ["value"]);
        InjectConstructor(attribute, [], []);
        InjectGetOnlyProperty(attribute, "Value", options);
    }

    private static void RestoreAssemblyVersion(ApplicationAnalysisContext appContext, AssemblyAnalysisContext corlib)
    {
        const string ns = "System.Reflection";
        if (corlib.GetTypeByFullName($"{ns}.AssemblyVersionAttribute") != null) return;
        var types = appContext.SystemTypes;

        var attribute = corlib.InjectType(ns, "AssemblyVersionAttribute", types.SystemAttributeType,
            TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.BeforeFieldInit);
        InjectConstructor(attribute, [types.SystemStringType], ["version"]);
        InjectGetOnlyProperty(attribute, "Version", types.SystemStringType);
    }

    private static void RestoreMathConstants(ApplicationAnalysisContext appContext, AssemblyAnalysisContext corlib)
    {
        if (corlib.GetTypeByFullName("System.Math") is not { } math) return;

        foreach (var (name, value) in new[] { ("PI", System.Math.PI), ("E", System.Math.E) })
        {
            if (math.Fields.Any(f => f.Name == name)) continue;
            math.Fields.Add(new InjectedFieldAnalysisContext(name, appContext.SystemTypes.SystemDoubleType,
                FieldAttributes.Public | FieldAttributes.Static | FieldAttributes.Literal | FieldAttributes.HasDefault, math,
                constantValue: value));
        }
    }

    internal static void RestoreAutoPropertyGetters(TypeAnalysisContext type)
    {
        foreach (var property in type.Properties)
        {
            if (property is not { Getter: null, Setter: { IsStatic: false } setter }
                || type.Fields.All(f => f.IsStatic || f.Name != $"<{property.Name}>k__BackingField" || f.FieldType != property.PropertyType))
                continue;

            var getter = new InjectedMethodAnalysisContext(type, $"get_{property.Name}", property.PropertyType,
                setter.Attributes & ~MethodAttributes.Abstract, []);
            type.Methods.Add(getter);
            property.Getter = getter;
        }
    }

    private static bool IsAttributeType(TypeAnalysisContext type)
    {
        for (var current = type.BaseType; current != null; current = current.BaseType)
            if (current is { Namespace: "System", Name: "Attribute" })
                return true;
        return false;
    }

    private static TypeAnalysisContext InjectEnum(ApplicationAnalysisContext appContext, AssemblyAnalysisContext corlib,
        string ns, string name, params (string Name, int Value)[] members)
    {
        var type = corlib.InjectType(ns, name, appContext.SystemTypes.EnumType, TypeAttributes.Public | TypeAttributes.Sealed);
        type.InjectFieldContext("value__", appContext.SystemTypes.SystemInt32Type,
            FieldAttributes.Public | FieldAttributes.SpecialName | FieldAttributes.RTSpecialName);
        foreach (var (memberName, value) in members)
            type.Fields.Add(new InjectedFieldAnalysisContext(memberName, type,
                FieldAttributes.Public | FieldAttributes.Static | FieldAttributes.Literal | FieldAttributes.HasDefault, type,
                constantValue: value));
        return type;
    }

    private static void InjectConstructor(InjectedTypeAnalysisContext type, TypeAnalysisContext[] parameters, string[] names)
        => type.Methods.Add(new InjectedMethodAnalysisContext(type, ".ctor", type.AppContext.SystemTypes.SystemVoidType,
            Constructor, parameters, names));

    private static void InjectGetOnlyProperty(InjectedTypeAnalysisContext type, string name, TypeAnalysisContext propertyType)
    {
        var getter = new InjectedMethodAnalysisContext(type, $"get_{name}", propertyType, Accessor, []);
        type.Methods.Add(getter);
        type.InjectPropertyContext(name, propertyType, getter, null, PropertyAttributes.None);
    }
}
