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
            if (GetSizeAndAlignment(fieldType, pointerSize, allowMetadataStructs: !definition.IsValueType) is not var (size, alignment))
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
                var layout = GetSizeAndAlignment(field.FieldType, pointerSize);
                // Base offsets are already supplied by metadata. An embedded non-generic
                // value type needs only its managed extent here, not an inferred alignment.
                var size = layout?.Size ?? (field.FieldType is { IsValueType: true, GenericParameters.Count: 0, Definition: not null }
                    and not GenericInstanceTypeAnalysisContext ? TypeSizes.UnboxedSize(field.FieldType, pointerSize) : 0);
                if (size <= 0 || field.Offset < 2L * pointerSize
                    || layout is { } known && field.Offset % known.Alignment != 0)
                    return null;
                end = Math.Max(end, field.Offset + size);
            }
        }
        // Only accept an exact metadata extent. Tail padding may be reused by a
        // derived class, so a rounded instance size is not a safe starting offset.
        return end == (metadataSize ?? (uint)(2 * pointerSize)) ? end : null;
    }

    private static (long Size, long Alignment)? GetSizeAndAlignment(TypeAnalysisContext fieldType, int pointerSize, bool allowMetadataStructs = false, int depth = 0)
    {
        if (depth > 16) return null;
        if (fieldType is GenericParameterTypeAnalysisContext or PointerTypeAnalysisContext || !fieldType.IsValueType)
            return (pointerSize, pointerSize);

        if (fieldType.IsEnumType && fieldType.Fields.FirstOrDefault(f => !f.IsStatic) is { } underlying)
            return GetSizeAndAlignment(underlying.FieldType, pointerSize, allowMetadataStructs, depth + 1);

        return fieldType.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte" => (1, 1),
            "System.Int16" or "System.UInt16" or "System.Char" => (2, 2),
            "System.Int32" or "System.UInt32" or "System.Single" => (4, 4),
            "System.Int64" or "System.UInt64" or "System.Double" => (8, 8),
            "System.IntPtr" or "System.UIntPtr" => (pointerSize, pointerSize),
            _ => allowMetadataStructs ? MetadataValueTypeLayout(fieldType, pointerSize, depth + 1) : null
        };
    }

    private static (long Size, long Alignment)? MetadataValueTypeLayout(TypeAnalysisContext type, int pointerSize, int depth)
    {
        // Infer natural alignment only for the 64-bit layout, where the scalar rules
        // above apply. 32-bit targets differ in their alignment of 64-bit members.
        if (pointerSize != 8 || type is GenericInstanceTypeAnalysisContext || type.GenericParameters.Count != 0
            || type.Definition is not { PackingSize: 0, ClassSizeIsDefault: true } metadata
            || (type.Attributes & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout)
            return null;
        var fields = type.Fields.Where(f => !f.IsStatic).ToArray();
        if (fields.Length == 0) return null;
        var end = 0L;
        var alignment = 1L;
        foreach (var field in fields)
        {
            if (GetSizeAndAlignment(field.FieldType, pointerSize, true, depth) is not { } layout) return null;
            end = (end + layout.Alignment - 1) & ~(layout.Alignment - 1);
            if (field.Offset != end) return null;
            end += layout.Size;
            alignment = Math.Max(alignment, layout.Alignment);
        }
        var size = (end + alignment - 1) & ~(alignment - 1);
        // Both every member offset and the complete managed size must agree. Native
        // marshalled sizes are not evidence for managed reference-containing structs.
        return size == (long)metadata.RawSizes.instance_size - 2L * pointerSize ? (size, alignment) : null;
    }

}
