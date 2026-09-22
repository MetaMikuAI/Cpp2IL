using System;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Utils;

// Consumes one scalar and leaves one converted scalar. Explicit bounds avoid
// depending on the CLR version's unspecified overflow result for conv.i*/u*.
internal static class NumericConversionEmitter
{
    internal static void Emit(CilMethodBody body, NumericConversion conversion)
    {
        var il = body.Instructions;
        var source = conversion.SourceType.FullName;
        var target = conversion.TargetType.FullName;
        var sourceFloat = source is "System.Single" or "System.Double";
        if (target is "System.Single" or "System.Double")
        {
            if (!sourceFloat)
            {
                il.Add(IntegerOpcode(source));
                if (source is "System.UInt32" or "System.UInt64") il.Add(CilOpCodes.Conv_R_Un);
            }
            var output = target == "System.Single" ? CilOpCodes.Conv_R4 : CilOpCodes.Conv_R8;
            il.Add(output);
            if (conversion.FractionalBits != 0)
            {
                if (target == "System.Single") il.Add(CilOpCodes.Ldc_R4, (float)Math.Pow(2.0, -conversion.FractionalBits));
                else il.Add(CilOpCodes.Ldc_R8, Math.Pow(2.0, -conversion.FractionalBits));
                il.Add(CilOpCodes.Mul);
                il.Add(output);
            }
            return;
        }
        if (!sourceFloat) throw new InvalidOperationException("Expected a floating-to-integer conversion");
        var integerOpcode = IntegerOpcode(target);
        var unsigned = target is "System.UInt32" or "System.UInt64";
        var wide = target is "System.Int64" or "System.UInt64";
        var factory = body.Owner!.DeclaringModule!.CorLibTypeFactory;
        var value = new CilLocalVariable(factory.Double);
        var result = new CilLocalVariable(wide ? (unsigned ? factory.UInt64 : factory.Int64) : (unsigned ? factory.UInt32 : factory.Int32));
        body.LocalVariables.Add(value);
        body.LocalVariables.Add(result);
        if (source == "System.Single") il.Add(CilOpCodes.Conv_R4);
        il.Add(CilOpCodes.Conv_R8);
        if (conversion.FractionalBits != 0)
        {
            il.Add(CilOpCodes.Ldc_R8, Math.Pow(2.0, conversion.FractionalBits));
            il.Add(CilOpCodes.Mul);
        }
        il.Add(CilOpCodes.Stloc, value);
        var done = new CilInstruction(CilOpCodes.Ldloc, result);
        var zero = new CilInstruction(CilOpCodes.Nop);
        var high = new CilInstruction(CilOpCodes.Nop);
        var low = new CilInstruction(CilOpCodes.Nop);
        void Branch(CilOpCode op, CilInstruction destination) => il.Add(op, new CilInstructionLabel(destination));
        void LoadInteger(long number)
        {
            if (wide) il.Add(CilOpCodes.Ldc_I8, number);
            else il.Add(CilOpCodes.Ldc_I4, unchecked((int)number));
        }
        void StoreAndFinish()
        {
            il.Add(CilOpCodes.Stloc, result);
            Branch(CilOpCodes.Br, done);
        }
        var upper = Math.Pow(2.0, (wide ? 64 : 32) - (unsigned ? 0 : 1));
        var minimum = unsigned ? 0 : wide ? long.MinValue : int.MinValue;
        var maximum = unsigned ? (wide ? -1L : uint.MaxValue) : (wide ? long.MaxValue : int.MaxValue);
        il.Add(CilOpCodes.Ldloc, value);
        il.Add(CilOpCodes.Ldloc, value);
        il.Add(CilOpCodes.Ceq);
        Branch(CilOpCodes.Brfalse, zero); // NaN is not equal to itself.
        il.Add(CilOpCodes.Ldloc, value);
        il.Add(CilOpCodes.Ldc_R8, upper);
        Branch(CilOpCodes.Bge, high);
        il.Add(CilOpCodes.Ldloc, value);
        il.Add(CilOpCodes.Ldc_R8, unsigned ? 0.0 : -upper);
        Branch(CilOpCodes.Ble, low);
        il.Add(CilOpCodes.Ldloc, value);
        il.Add(integerOpcode);
        il.Add(CilOpCodes.Stloc, result);
        if (conversion.Rounding != NumericRounding.Truncate)
        {
            var fraction = new CilLocalVariable(factory.Double);
            body.LocalVariables.Add(fraction);
            il.Add(CilOpCodes.Ldloc, value);
            il.Add(CilOpCodes.Ldloc, result);
            if (unsigned) il.Add(CilOpCodes.Conv_R_Un);
            il.Add(CilOpCodes.Conv_R8);
            il.Add(CilOpCodes.Sub);
            il.Add(CilOpCodes.Stloc, fraction);
            var increment = new CilInstruction(CilOpCodes.Nop);
            var decrement = new CilInstruction(CilOpCodes.Nop);
            void CompareFraction(double bound, CilOpCode operation, CilInstruction destination)
            {
                il.Add(CilOpCodes.Ldloc, fraction);
                il.Add(CilOpCodes.Ldc_R8, bound);
                Branch(operation, destination);
            }
            switch (conversion.Rounding)
            {
                case NumericRounding.Floor: CompareFraction(0, CilOpCodes.Blt, decrement); break;
                case NumericRounding.Ceiling: CompareFraction(0, CilOpCodes.Bgt, increment); break;
                case NumericRounding.NearestAway:
                    CompareFraction(0.5, CilOpCodes.Bge, increment);
                    CompareFraction(-0.5, CilOpCodes.Ble, decrement);
                    break;
                case NumericRounding.NearestEven:
                    CompareFraction(0.5, CilOpCodes.Bgt, increment);
                    CompareFraction(-0.5, CilOpCodes.Blt, decrement);
                    il.Add(CilOpCodes.Ldloc, fraction);
                    il.Add(CilOpCodes.Ldc_R8, 0.5);
                    il.Add(CilOpCodes.Ceq);
                    il.Add(CilOpCodes.Ldloc, fraction);
                    il.Add(CilOpCodes.Ldc_R8, -0.5);
                    il.Add(CilOpCodes.Ceq);
                    il.Add(CilOpCodes.Or);
                    Branch(CilOpCodes.Brfalse, done);
                    il.Add(CilOpCodes.Ldloc, result);
                    LoadInteger(1);
                    il.Add(CilOpCodes.And);
                    Branch(CilOpCodes.Brfalse, done); // even ties stay at the truncated value.
                    CompareFraction(0, CilOpCodes.Bgt, increment);
                    Branch(CilOpCodes.Br, decrement);
                    break;
                default: throw new InvalidOperationException("Unsupported numeric rounding mode");
            }
            Branch(CilOpCodes.Br, done);
            il.Add(increment);
            il.Add(CilOpCodes.Ldloc, result);
            LoadInteger(maximum);
            Branch(CilOpCodes.Beq, done);
            il.Add(CilOpCodes.Ldloc, result);
            LoadInteger(1);
            il.Add(CilOpCodes.Add);
            StoreAndFinish();
            il.Add(decrement);
            il.Add(CilOpCodes.Ldloc, result);
            LoadInteger(minimum);
            Branch(CilOpCodes.Beq, done);
            il.Add(CilOpCodes.Ldloc, result);
            LoadInteger(1);
            il.Add(CilOpCodes.Sub);
            StoreAndFinish();
        }
        else Branch(CilOpCodes.Br, done);
        il.Add(zero);
        LoadInteger(0);
        StoreAndFinish();
        il.Add(high);
        LoadInteger(maximum);
        StoreAndFinish();
        il.Add(low);
        LoadInteger(minimum);
        StoreAndFinish();
        il.Add(done);
    }

    private static CilOpCode IntegerOpcode(string type) => type switch
    {
        "System.Int32" => CilOpCodes.Conv_I4, "System.UInt32" => CilOpCodes.Conv_U4,
        "System.Int64" => CilOpCodes.Conv_I8, "System.UInt64" => CilOpCodes.Conv_U8,
        _ => throw new InvalidOperationException($"Unsupported numeric conversion type: {type}")
    };
}
