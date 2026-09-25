using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Utils;

// integer args in X0-X7, fp args in V0-V7 (independent counters), rest on the stack.
// Oversized struct returns go via a pointer in X8, which is not an argument register.
public class Arm64CallingConventionResolver : BaseCallingConventionResolver
{
    private const int PtrSize = 8;

    // AAPCS64 6.1.1: a call may overwrite X0-X17 and V0-V7, V16-V31 (only the low 64 bits of
    // V8-V15 survive, and ISIL does not model the upper halves of those).
    internal static readonly string[] CallerSavedRegisters =
    [
        .. Enumerable.Range(0, 18).Select(n => $"X{n}"),
        .. Enumerable.Range(0, 8).Select(n => $"V{n}"),
        .. Enumerable.Range(16, 16).Select(n => $"V{n}")
    ];

    private static readonly string[] IntegerRegisters = ["X0", "X1", "X2", "X3", "X4", "X5", "X6", "X7"];
    private static readonly string[] FloatRegisters = ["V0", "V1", "V2", "V3", "V4", "V5", "V6", "V7"];

    public override Register ReturnRegister(MethodAnalysisContext ctx)
        => new(null, IsFloatingPoint(ctx.ReturnType) ? "V0" : "X0");

    public override Register? HiddenReturnBufferRegister(MethodAnalysisContext ctx)
        => ReturnsViaHiddenBuffer(ctx) ? new Register(null, "X8") : null;

    public override bool ReturnsViaHiddenBuffer(MethodAnalysisContext ctx)
    {
        if (ctx.IsVoid)
            return false;

        var returnType = ctx.ReturnType;
        if (!returnType.IsValueType || IsFloatingPoint(returnType) || FloatingAggregateFields(returnType) != null)
            return false;

        var size = TypeSizes.UnboxedSize(returnType, PtrSize);
        if (size == 0)
            return false; // unknown size (e.g. generic), assume a register return

        return size > 16;
    }

    protected override (string[] Integer, string[] Float) RawRegisters(ApplicationAnalysisContext app)
        => (IntegerRegisters, FloatRegisters);

    protected override bool HiddenBufferConsumesArgumentSlot => false;

    protected override int IntegerArgumentSlots(ParameterAnalysisContext parameter)
        => IntegerArgumentSlots(parameter.ParameterType);

    internal static int IntegerArgumentSlots(TypeAnalysisContext type)
        => IntegerCompositeRegisters(type) is { Length: 2 } ? 2 : 1;

    // AAPCS64 C.10/C.12: a composite of 9 to 16 bytes that is not an HFA occupies two consecutive
    // X registers, each holding the next 8 bytes of the value's memory image. Returns the members
    // (flattened through nested value types) each register carries. Only an ordinary sequential
    // layout is proven; packed, explicit, generic and unknown layouts yield null.
    internal static (long Offset, int Size)[][]? IntegerCompositeRegisters(TypeAnalysisContext type)
    {
        if (!type.IsValueType || type.IsEnumType || type.AppContext.Binary.PointerSizeBytes != PtrSize
            || TypeSizes.UnboxedSize(type, PtrSize) is not (> 8 and <= 16))
            return null;
        var leaves = new List<(long Offset, int Size, bool Float)>();
        if (FlattenMembers(type, 0, leaves, 0) == null || leaves.Count == 0)
            return null;
        // Members of one floating-point type form an HFA, which travels in SIMD registers.
        if (leaves.All(l => l.Float && l.Size == leaves[0].Size))
            return null;
        return
        [
            leaves.Where(l => l.Offset < PtrSize).Select(l => (l.Offset, l.Size)).ToArray(),
            leaves.Where(l => l.Offset >= PtrSize).Select(l => (l.Offset, l.Size)).ToArray()
        ];
    }

    // The member each register of an integer composite carries, when each carries exactly one
    // (starting at the register's first byte); the rest of that register is padding.
    internal static (long Offset, int Size)[]? IntegerCompositeMembers(TypeAnalysisContext type)
        => IntegerCompositeRegisters(type) is [[var low], [var high]] && low.Offset == 0 && high.Offset == PtrSize
            ? [low, high]
            : null;

    // Appends the scalar members of type at start; returns the type's alignment, or null.
    private static long? FlattenMembers(TypeAnalysisContext type, long start, List<(long Offset, int Size, bool Float)> leaves, int depth)
    {
        if (depth > 4 || type is GenericInstanceTypeAnalysisContext || type.GenericParameters.Count != 0
            || type.Definition is not { PackingSize: 0, ClassSizeIsDefault: true }
            || (type.Attributes & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout)
            return null;
        var offset = 0L;
        var alignment = 1L;
        foreach (var field in type.Fields.Where(f => !f.IsStatic).OrderBy(f => f.Offset))
        {
            var fieldType = field.FieldType;
            long size, fieldAlignment;
            if (!fieldType.IsValueType)
            {
                size = fieldAlignment = PtrSize;
                leaves.Add((start + field.Offset, PtrSize, false));
            }
            else if (fieldType.IsEnumType || ScalarSize(fieldType) != 0)
            {
                size = fieldAlignment = fieldType.IsEnumType ? TypeSizes.UnboxedSize(fieldType, PtrSize) : ScalarSize(fieldType);
                if (size is not (1 or 2 or 4 or 8))
                    return null;
                leaves.Add((start + field.Offset, (int)size, !fieldType.IsEnumType && IsFloatingPoint(fieldType)));
            }
            else if (fieldType.Type == Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE)
            {
                size = TypeSizes.UnboxedSize(fieldType, PtrSize);
                if (size <= 0 || FlattenMembers(fieldType, start + field.Offset, leaves, depth + 1) is not { } nested)
                    return null;
                fieldAlignment = nested;
            }
            else return null;

            alignment = System.Math.Max(alignment, fieldAlignment);
            offset = (offset + fieldAlignment - 1) & -fieldAlignment;
            if (field.Offset != offset)
                return null;
            offset += size;
        }
        return ((offset + alignment - 1) & -alignment) == TypeSizes.UnboxedSize(type, PtrSize) ? alignment : null;
    }

    private static long ScalarSize(TypeAnalysisContext type) => type.FullName switch
    {
        "System.Boolean" or "System.Byte" or "System.SByte" => 1,
        "System.Char" or "System.Int16" or "System.UInt16" => 2,
        "System.Int32" or "System.UInt32" or "System.Single" => 4,
        "System.Int64" or "System.UInt64" or "System.IntPtr" or "System.UIntPtr" or "System.Double" => 8,
        _ => 0
    };

    // Flat homogeneous floating aggregates use consecutive SIMD registers, not X registers.
    internal static FieldAnalysisContext[]? FloatingAggregateFields(TypeAnalysisContext type)
    {
        if (!type.IsValueType || IsFloatingPoint(type) || type.IsEnumType || type is GenericInstanceTypeAnalysisContext
            || type.GenericParameters.Count != 0 || type.Definition is not { PackingSize: 0 }
            || (type.Attributes & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout)
            return null;
        var fields = type.Fields.Where(f => !f.IsStatic).OrderBy(f => f.Offset).ToArray();
        if (fields.Length is < 1 or > 4) return null;
        var scalar = fields[0].FieldType;
        var size = scalar.FullName == "System.Single" ? 4 : scalar.FullName == "System.Double" ? 8 : 0;
        if (size == 0 || fields.Where((f, i) => f.FieldType != scalar || f.Offset != i * size).Any()
            || TypeSizes.UnboxedSize(type, PtrSize) != fields.Length * size) return null;
        return fields;
    }

    public override IOperand[] ResolveForManaged(MethodAnalysisContext ctx)
    {
        var args = new List<IOperand>();

        var integer = 0;
        var floating = 0;
        var stack = 0;

        void AddParameter(ParameterAnalysisContext? par)
        {
            var slots = par == null ? 1 : IntegerArgumentSlots(par);
            if (par != null && FloatingAggregateFields(par.ParameterType) is { } fields)
            {
                if (floating + fields.Length <= FloatRegisters.Length)
                {
                    args.Add(new Register(null, FloatRegisters[floating]));
                    floating += fields.Length;
                    return;
                }
                floating = FloatRegisters.Length;
                args.Add(new StackOffset(stack));
                stack += (int)((TypeSizes.UnboxedSize(par.ParameterType, PtrSize) + 7) & ~7L);
                return;
            }
            if (par != null && IsFloatingPoint(par))
            {
                if (floating < FloatRegisters.Length)
                {
                    args.Add(new Register(null, FloatRegisters[floating++]));
                    return;
                }
            }
            else if (integer + slots <= IntegerRegisters.Length)
            {
                args.Add(new Register(null, IntegerRegisters[integer]));
                integer += slots;
                return;
            }
            else integer = IntegerRegisters.Length;

            args.Add(new StackOffset(stack));
            stack += PtrSize * slots;
        }

        if (!ctx.IsStatic)
            AddParameter(null);

        foreach (var par in ctx.Parameters)
            AddParameter(par);

        AddParameter(null); // The MethodInfo argument

        return args.ToArray();
    }
}
