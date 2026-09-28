using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;

namespace Cpp2IL.Core.Analysis;

public static class ProvenGetterReadRecovery
{
    public readonly record struct Result(int Getters, int Reads);

    public static Result Recover(ModuleDefinition module, bool apply = true)
    {
        var getters = new Dictionary<FieldDefinition, MethodDefinition>();
        foreach (var property in module.GetAllTypes().SelectMany(t => t.Properties))
        {
            var getter = property.GetMethod;
            if (getter is not { IsPublic: true, IsVirtual: false, GenericParameters.Count: 0, CilMethodBody: { } body }
                || getter.IsPInvokeImpl || (getter.ImplAttributes & MethodImplAttributes.Synchronized) != 0
                || getter.Signature is not { ParameterTypes.Count: 0, ReturnType: not ByReferenceTypeSignature }
                || getter.DeclaringType is not { IsValueType: false, GenericParameters.Count: 0 } owner
                || body.ExceptionHandlers.Count != 0)
                continue;

            var il = body.Instructions;
            var fieldIndex = getter.IsStatic ? 0 : 1;
            if (il.Count != fieldIndex + 2 || il[^1].OpCode != CilOpCodes.Ret
                || !getter.IsStatic && il[0].OpCode != CilOpCodes.Ldarg_0
                || il[fieldIndex].OpCode != (getter.IsStatic ? CilOpCodes.Ldsfld : CilOpCodes.Ldfld)
                || il[fieldIndex].Operand is not FieldDefinition field
                || field.DeclaringType != owner || field.DeclaringModule != module
                || field.IsStatic != getter.IsStatic || field.IsPublic
                || !SignatureComparer.Default.Equals(field.Signature!.FieldType, getter.Signature.ReturnType))
                continue;

            getters.TryAdd(field, getter);
        }

        var reads = 0;
        foreach (var method in module.GetAllTypes().SelectMany(t => t.Methods))
        {
            // Calling through an uninitialized this can change constructor verification.
            if (method.Name == ".ctor" || method.CilMethodBody is not { } body)
                continue;
            var il = body.Instructions;
            for (var i = 0; i < il.Count; i++)
            {
                var instruction = il[i];
                if (instruction.OpCode != CilOpCodes.Ldfld && instruction.OpCode != CilOpCodes.Ldsfld
                    || i > 0 && il[i - 1].OpCode.OpCodeType == CilOpCodeType.Prefix
                    || instruction.Operand is not FieldDefinition field || !getters.TryGetValue(field, out var getter)
                    || method == getter || method.DeclaringModule != getter.DeclaringModule)
                    continue;
                reads++;
                if (apply)
                {
                    instruction.OpCode = getter.IsStatic ? CilOpCodes.Call : CilOpCodes.Callvirt;
                    instruction.Operand = getter;
                }
            }
        }
        return new Result(getters.Count, reads);
    }
}
