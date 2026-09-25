using System;
using System.Collections.Generic;
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
        => ComputeLayout(definition)?.Slots.FirstOrDefault(s => s.Offset == targetOffset)?.Definition;

    /// <summary>An instance field of a computed layout, at its offset from the receiver's storage.</summary>
    public sealed record FieldSlot(FieldAnalysisContext Definition, FieldAnalysisContext Field, long Offset, long Size);

    /// <summary>
    /// Lays out the instance fields of a generic definition or instance as the IL2CPP runtime does:
    /// in declaration order, each at its natural alignment after the base storage. A value type is
    /// addressed unboxed, so its first field starts at 0 rather than after an object header. Fields
    /// of an instance are bound to it so their types are substituted. The slots stop before the first
    /// field whose size and alignment cannot be proven, since every later offset depends on it;
    /// <c>Complete</c> reports whether all fields were laid out, and <c>End</c> where the last one ends.
    /// </summary>
    public static (List<FieldSlot> Slots, bool Complete, long End)? ComputeLayout(TypeAnalysisContext type)
    {
        var instance = type as GenericInstanceTypeAnalysisContext;
        var definition = instance?.GenericType ?? type;
        var pointerSize = definition.AppContext.Binary.PointerSizeBytes;

        if ((definition.Attributes & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout
            || definition.Definition is { PackingSize: > 0 })
            return null;
        long offset;
        if (definition.IsValueType)
        {
            // An explicit class size may pad or truncate the natural extent.
            if (definition.Definition is { ClassSizeIsDefault: false })
                return null;
            offset = 0;
        }
        else if (BaseStorageEnd(instance?.BaseType ?? definition.BaseType, pointerSize) is { } baseEnd)
            offset = baseEnd;
        else
            return null;

        var slots = new List<FieldSlot>();
        foreach (var field in definition.Fields)
        {
            if (field.IsStatic)
                continue;

            // Substitute before measuring: T may be inline, while T[] remains a pointer
            // even when T is a value type with an otherwise unknown layout.
            var fieldType = instance == null ? field.FieldType
                : GenericInstantiation.Instantiate(field.FieldType, instance.GenericArguments, []);
            if (GetSizeAndAlignment(fieldType, pointerSize, allowMetadataStructs: true) is not var (size, alignment))
                return (slots, false, offset);

            offset = (offset + alignment - 1) & ~(alignment - 1);
            slots.Add(new(field, instance == null ? field : new ConcreteGenericFieldAnalysisContext(field, instance), offset, size));
            offset += size;
        }

        return (slots, true, offset);
    }

    /// <summary>
    /// The unboxed size and alignment of a value type, or null if its layout is not proven. Scalars
    /// and enums have fixed sizes, a non-generic struct must agree with its metadata, and a generic
    /// instance is laid out from its substituted field types.
    /// </summary>
    public static (long Size, long Alignment)? ValueTypeSizeAndAlignment(TypeAnalysisContext type)
        => type.IsValueType ? GetSizeAndAlignment(type, type.AppContext.Binary.PointerSizeBytes, allowMetadataStructs: true) : null;

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
            _ => !allowMetadataStructs ? null
                : fieldType is GenericInstanceTypeAnalysisContext instance ? GenericValueTypeLayout(instance, pointerSize, depth + 1)
                : MetadataValueTypeLayout(fieldType, pointerSize, depth + 1)
        };
    }

    private static (long Size, long Alignment)? GenericValueTypeLayout(GenericInstanceTypeAnalysisContext instance, int pointerSize, int depth)
    {
        // Instantiations carry no metadata size, so the natural layout is only inferred for the
        // 64-bit rules above, where the runtime aligns each field to its own alignment.
        var definition = instance.GenericType;
        if (pointerSize != 8 || depth > 16 || definition.Definition is not { PackingSize: 0, ClassSizeIsDefault: true }
            || (definition.Attributes & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout)
            return null;
        var end = 0L;
        var alignment = 1L;
        var any = false;
        foreach (var field in definition.Fields.Where(f => !f.IsStatic))
        {
            var fieldType = GenericInstantiation.Instantiate(field.FieldType, instance.GenericArguments, []);
            if (GetSizeAndAlignment(fieldType, pointerSize, true, depth) is not { } layout) return null;
            end = (end + layout.Alignment - 1) & ~(layout.Alignment - 1);
            end += layout.Size;
            alignment = Math.Max(alignment, layout.Alignment);
            any = true;
        }
        // An empty struct still occupies storage, but its size is not a field layout to infer.
        return any ? ((end + alignment - 1) & ~(alignment - 1), alignment) : null;
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
