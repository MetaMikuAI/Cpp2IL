using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

//Resolves field offsets on generic types, which are all 0 in the metadata.
public static class GenericInstanceFieldLayout
{
    public static FieldAnalysisContext? FindFieldAtOffset(TypeAnalysisContext definition, long targetOffset, IReadOnlyList<TypeAnalysisContext>? genericArguments = null)
    {
        var pointerSize = definition.AppContext.Binary.PointerSizeBytes;

        // TODO Support anything outside the trivial case.
        for (var baseType = definition.BaseType; baseType != null; baseType = baseType.BaseType)
            if (baseType.Fields.Any(f => !f.IsStatic))
                return null;

        // Value types have no object header; fields start at offset 0.
        var offset = definition.IsValueType ? 0 : 2L * pointerSize;

        foreach (var field in definition.Fields)
        {
            if (field.IsStatic)
                continue;

            if (GetSizeAndAlignment(field.FieldType, pointerSize, genericArguments) is not var (size, alignment))
                return null;

            offset = (offset + alignment - 1) & ~(alignment - 1);

            if (offset == targetOffset)
                return field;

            offset += size;
        }

        return null;
    }

    private static (long Size, long Alignment)? GetSizeAndAlignment(TypeAnalysisContext fieldType, int pointerSize, IReadOnlyList<TypeAnalysisContext>? genericArguments)
    {
        // A bare T field is laid out as the generic argument it stands for: inlined when the
        // argument is a value type (e.g. List<int> still stores T[] _items by reference, but
        // KeyValuePair<int, int> inlines both), a pointer otherwise.
        if (fieldType is GenericParameterTypeAnalysisContext genericParameter
            && genericArguments != null
            && genericParameter.Index < genericArguments.Count)
            fieldType = genericArguments[genericParameter.Index];

        // TODO support user-defined value types
        if (fieldType is GenericParameterTypeAnalysisContext or PointerTypeAnalysisContext || !fieldType.IsValueType)
            return (pointerSize, pointerSize);

        if (fieldType.IsEnumType && fieldType.Fields.FirstOrDefault(f => !f.IsStatic) is { } underlying)
            return GetSizeAndAlignment(underlying.FieldType, pointerSize, genericArguments);

        var primitive = fieldType.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte" => ((long Size, long Alignment)?)(1, 1),
            "System.Int16" or "System.UInt16" or "System.Char" => (2, 2),
            "System.Int32" or "System.UInt32" or "System.Single" => (4, 4),
            "System.Int64" or "System.UInt64" or "System.Double" => (8, 8),
            "System.IntPtr" or "System.UIntPtr" => (pointerSize, pointerSize),
            _ => null
        };

        if (primitive != null)
            return primitive;

        // A user-defined struct: compute its layout from its fields. Size is the aligned sum,
        // alignment is the largest field alignment - matching the CLI's sequential layout.
        long size = 0;
        long alignment = 1;

        for (var type = fieldType; type != null; type = type.BaseType)
        {
            foreach (var field in type.Fields)
            {
                if (field.IsStatic)
                    continue;

                if (GetSizeAndAlignment(field.FieldType, pointerSize, genericArguments) is not var (fieldSize, fieldAlign))
                    return null;

                alignment = Math.Max(alignment, fieldAlign);
                size = (size + fieldAlign - 1) & ~(fieldAlign - 1);
                size += fieldSize;
            }
        }

        if (size == 0)
            return null;

        return ((size + alignment - 1) & ~(alignment - 1), alignment);
    }
}
