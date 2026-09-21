using System;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

//Resolves field offsets on generic types, which are all 0 in the metadata.
public static class GenericInstanceFieldLayout
{
    public static FieldAnalysisContext? FindFieldAtUnboxedOffset(TypeAnalysisContext definition, long targetOffset)
    {
        var pointerSize = definition.AppContext.Binary.PointerSizeBytes;
        var offset = 0L;

        foreach (var field in definition.Fields.Where(f => !f.IsStatic))
        {
            if (GetSizeAndAlignment(field.FieldType, pointerSize) is not var (size, alignment))
                return null;

            offset = (offset + alignment - 1) & ~(alignment - 1);
            if (offset == targetOffset)
                return field;

            offset += size;
        }

        return null;
    }

    public static FieldAnalysisContext? FindFieldAtOffset(TypeAnalysisContext definition, long targetOffset)
    {
        var instance = definition as GenericInstanceTypeAnalysisContext;
        definition = instance?.GenericType ?? definition;
        var pointerSize = definition.AppContext.Binary.PointerSizeBytes;

        if ((definition.Attributes & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout
            || definition.Definition is { PackingSize: > 0 })
            return null;
        if (BaseStorageEnd(instance?.BaseType ?? definition.BaseType, pointerSize) is not { } offset)
            return null;

        foreach (var field in definition.Fields)
        {
            if (field.IsStatic)
                continue;

            // Substitute before measuring: T may be inline, while T[] remains a pointer
            // even when T is a value type with an otherwise unknown layout.
            var fieldType = instance == null ? field.FieldType
                : GenericInstantiation.Instantiate(field.FieldType, instance.GenericArguments, []);
            if (GetSizeAndAlignment(fieldType, pointerSize) is not var (size, alignment))
                return null;

            offset = (offset + alignment - 1) & ~(alignment - 1);

            if (offset == targetOffset)
                return field;

            offset += size;
        }

        return null;
    }

    private static long? BaseStorageEnd(TypeAnalysisContext? type, int pointerSize)
    {
        var end = 2L * pointerSize;
        uint? metadataSize = null;
        for (; type != null; type = type.BaseType)
        {
            var definition = (type as GenericInstanceTypeAnalysisContext)?.GenericType ?? type;
            if ((definition.Attributes & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout
                || definition.Definition is { PackingSize: > 0 } or { ClassSizeIsDefault: false })
                return null;
            var fields = definition.Fields.Where(f => !f.IsStatic).ToList();
            if (type is GenericInstanceTypeAnalysisContext || definition.GenericParameters.Count > 0)
            {
                // A fieldless generic wrapper adds no storage. Instantiated base fields
                // still need a complete layout, not the definition's zero offsets.
                if (fields.Count != 0)
                    return null;
                continue;
            }
            // System.Object contributes the target's two-pointer header, not fields.
            if (definition.Definition is { } metadata && definition != type.AppContext.SystemTypes.SystemObjectType)
                metadataSize ??= metadata.RawSizes.instance_size;
            else if (fields.Count != 0)
                return null;
            foreach (var field in fields)
            {
                if (GetSizeAndAlignment(field.FieldType, pointerSize) is not { } layout
                    || field.Offset < 2L * pointerSize || field.Offset % layout.Alignment != 0)
                    return null;
                end = Math.Max(end, field.Offset + layout.Size);
            }
        }
        // Only accept an exact metadata extent. Tail padding may be reused by a
        // derived class, so a rounded instance size is not a safe starting offset.
        return end == (metadataSize ?? (uint)(2 * pointerSize)) ? end : null;
    }

    private static (long Size, long Alignment)? GetSizeAndAlignment(TypeAnalysisContext fieldType, int pointerSize)
    {
        // TODO support user-defined value types
        if (fieldType is GenericParameterTypeAnalysisContext or PointerTypeAnalysisContext || !fieldType.IsValueType)
            return (pointerSize, pointerSize);

        if (fieldType.IsEnumType && fieldType.Fields.FirstOrDefault(f => !f.IsStatic) is { } underlying)
            return GetSizeAndAlignment(underlying.FieldType, pointerSize);

        return fieldType.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte" => (1, 1),
            "System.Int16" or "System.UInt16" or "System.Char" => (2, 2),
            "System.Int32" or "System.UInt32" or "System.Single" => (4, 4),
            "System.Int64" or "System.UInt64" or "System.Double" => (8, 8),
            "System.IntPtr" or "System.UIntPtr" => (pointerSize, pointerSize),
            _ => null // an arbitrary struct needs its own layout computed, bail rather than guess
        };
    }
}
