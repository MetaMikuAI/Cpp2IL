using AsmResolver.DotNet.Code.Cil;
using AsmResolver.PE.DotNet.Cil;

namespace Cpp2IL.Core.Utils;

// Consume two Int64 values and leave the signed high half without requiring Int128 in the target runtime.
internal static class MultiplyHighEmitter
{
    internal static void Emit(CilMethodBody body)
    {
        var il = body.Instructions;
        CilLocalVariable Local()
        {
            var local = new CilLocalVariable(body.Owner!.DeclaringModule!.CorLibTypeFactory.Int64);
            body.LocalVariables.Add(local);
            return local;
        }
        var x = Local(); var y = Local();
        var xLow = Local(); var yLow = Local();
        var xHigh = Local(); var yHigh = Local();
        var cross = Local();
        il.Add(CilOpCodes.Stloc, y);
        il.Add(CilOpCodes.Stloc, x);
        void Split(CilLocalVariable value, CilLocalVariable low, CilLocalVariable high)
        {
            il.Add(CilOpCodes.Ldloc, value); il.Add(CilOpCodes.Conv_U4); il.Add(CilOpCodes.Conv_U8);
            il.Add(CilOpCodes.Stloc, low);
            il.Add(CilOpCodes.Ldloc, value); il.Add(CilOpCodes.Ldc_I4, 32); il.Add(CilOpCodes.Shr);
            il.Add(CilOpCodes.Stloc, high);
        }
        void Product(CilLocalVariable left, CilLocalVariable right)
        {
            il.Add(CilOpCodes.Ldloc, left); il.Add(CilOpCodes.Ldloc, right); il.Add(CilOpCodes.Mul);
        }
        Split(x, xLow, xHigh);
        Split(y, yLow, yHigh);
        // cross = xHigh * yLow + unsigned_high32(xLow * yLow).
        Product(xHigh, yLow);
        Product(xLow, yLow); il.Add(CilOpCodes.Ldc_I4, 32); il.Add(CilOpCodes.Shr_Un);
        il.Add(CilOpCodes.Add); il.Add(CilOpCodes.Stloc, cross);
        // high = xHigh*yHigh + (cross >> 32) + ((xLow*yHigh + unsigned_low32(cross)) >> 32).
        Product(xHigh, yHigh);
        il.Add(CilOpCodes.Ldloc, cross); il.Add(CilOpCodes.Ldc_I4, 32); il.Add(CilOpCodes.Shr);
        il.Add(CilOpCodes.Add);
        Product(xLow, yHigh);
        il.Add(CilOpCodes.Ldloc, cross); il.Add(CilOpCodes.Conv_U4); il.Add(CilOpCodes.Conv_U8);
        il.Add(CilOpCodes.Add); il.Add(CilOpCodes.Ldc_I4, 32); il.Add(CilOpCodes.Shr);
        il.Add(CilOpCodes.Add);
    }
}
