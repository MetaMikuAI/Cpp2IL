using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils;

// integer args in X0-X7, fp args in V0-V7 (independent counters), rest on the stack.
// Oversized struct returns go via a pointer in X8, which is not an argument register.
public class Arm64CallingConventionResolver : BaseCallingConventionResolver
{
    private const int PtrSize = 8;

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
        if (!returnType.IsValueType || IsFloatingPoint(returnType))
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
    {
        // AAPCS64 C.12: an integer composite occupies consecutive X registers.
        // Prove an ordinary flat integral/reference layout; HFA, packed, explicit
        // and unknown layouts must not be classified by size alone.
        if (!type.IsValueType || type.IsEnumType || type is GenericInstanceTypeAnalysisContext
            || type.GenericParameters.Count != 0 || type.AppContext.Binary.PointerSizeBytes != PtrSize
            || type.Definition is not { PackingSize: 0, ClassSizeIsDefault: true }
            || (type.Attributes & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout
            || TypeSizes.UnboxedSize(type, PtrSize) is not (> 8 and <= 16)) return 1;
        var offset = 0;
        var alignment = 1;
        foreach (var field in type.Fields.Where(f => !f.IsStatic).OrderBy(f => f.Offset))
        {
            var size = !field.FieldType.IsValueType ? PtrSize : field.FieldType.FullName switch
            {
                "System.Boolean" or "System.Byte" or "System.SByte" => 1,
                "System.Char" or "System.Int16" or "System.UInt16" => 2,
                "System.Int32" or "System.UInt32" => 4,
                "System.Int64" or "System.UInt64" or "System.IntPtr" or "System.UIntPtr" => 8,
                _ => 0
            };
            if (size == 0) return 1;
            alignment = System.Math.Max(alignment, size);
            offset = (offset + size - 1) & -size;
            if (field.Offset != offset) return 1;
            offset += size;
        }
        return ((offset + alignment - 1) & -alignment) == TypeSizes.UnboxedSize(type, PtrSize) ? 2 : 1;
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
