using System.Linq;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils;

public static class TypeSizes
{
    // Unboxed size of a value type, so the metadata's boxed size - the two pointer fields in the header. 0 if we
    // don't know (no definition, e.g. an open generic).
    public static long UnboxedSize(TypeAnalysisContext type, int pointerSize)
    {
        var header = 2L * pointerSize;

        if (type.Definition?.RawSizes is { instance_size: var boxed } && boxed > header)
            return boxed - header;

        if (type is GenericInstanceTypeAnalysisContext generic && generic.IsValueType)
            return GenericUnboxedSize(generic);

        return 0;
    }

    private static long GenericUnboxedSize(GenericInstanceTypeAnalysisContext generic)
    {
        var pointerSize = generic.AppContext.Binary.PointerSizeBytes;
        var offset = 0L;
        var maxAlignment = 1L;

        foreach (var field in generic.GenericType.Fields.Where(f => !f.IsStatic))
        {
            var fieldType = GenericInstantiation.Instantiate(field.FieldType, generic.GenericArguments, []);
            if (FieldSizeAndAlignment(fieldType, pointerSize) is not { } layout)
                return 0;

            maxAlignment = System.Math.Max(maxAlignment, layout.Alignment);
            offset = Align(offset, layout.Alignment);
            offset += layout.Size;
        }

        return Align(offset, maxAlignment);
    }

    private static (long Size, long Alignment)? FieldSizeAndAlignment(TypeAnalysisContext type, int pointerSize)
    {
        if (!type.IsValueType)
            return (pointerSize, pointerSize);

        if (type is GenericInstanceTypeAnalysisContext nestedGeneric)
        {
            var size = GenericUnboxedSize(nestedGeneric);
            return size == 0 ? null : (size, System.Math.Min(size, pointerSize));
        }

        var sizeFromMetadata = UnboxedSize(type, pointerSize);
        if (sizeFromMetadata == 0)
            return type.FullName switch
            {
                "System.Boolean" or "System.Byte" or "System.SByte" => (1, 1),
                "System.Int16" or "System.UInt16" or "System.Char" => (2, 2),
                "System.Int32" or "System.UInt32" or "System.Single" => (4, 4),
                "System.Int64" or "System.UInt64" or "System.Double" => (8, 8),
                "System.IntPtr" or "System.UIntPtr" => (pointerSize, pointerSize),
                _ => null
            };

        return (sizeFromMetadata, System.Math.Min(sizeFromMetadata, pointerSize));
    }

    private static long Align(long value, long alignment) => (value + alignment - 1) & ~(alignment - 1);
}
