using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Collections;
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
                || getter.DeclaringType is not { GenericParameters.Count: 0 } owner
                || body.ExceptionHandlers.Count != 0)
                continue;

            // The generator leaves nops where analysis removed instructions, and branches bridging to the next block.
            var il = body.Instructions.Where(i => i.OpCode != CilOpCodes.Nop).ToList();
            il = il.Where((i, index) => !(i.OpCode == CilOpCodes.Br && i.Operand is CilInstructionLabel { Instruction: { } to }
                                          && index + 1 < il.Count && to == il[index + 1])).ToList();
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

        var setters = ProvenSetters(module);

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
                // A store through a class's proven setter: stfld takes the same stack as the call.
                if (instruction.OpCode == CilOpCodes.Stfld || instruction.OpCode == CilOpCodes.Stsfld)
                {
                    if (!(i > 0 && il[i - 1].OpCode.OpCodeType == CilOpCodeType.Prefix)
                        && instruction.Operand is FieldDefinition stored && setters.TryGetValue(stored, out var setter)
                        && method != setter && method.DeclaringModule == setter.DeclaringModule
                        // The owner and its nested types may write the field themselves.
                        && !Within(method.DeclaringType, setter.DeclaringType!))
                    {
                        reads++;
                        if (apply)
                        {
                            instruction.OpCode = setter.IsStatic ? CilOpCodes.Call : CilOpCodes.Callvirt;
                            instruction.Operand = setter;
                        }
                    }
                    continue;
                }
                if (instruction.OpCode != CilOpCodes.Ldfld && instruction.OpCode != CilOpCodes.Ldsfld
                    || i > 0 && il[i - 1].OpCode.OpCodeType == CilOpCodeType.Prefix
                    || instruction.Operand is not FieldDefinition field || !getters.TryGetValue(field, out var getter)
                    || method == getter || method.DeclaringModule != getter.DeclaringModule)
                    continue;
                // A struct's getter takes its receiver by address, which the read must already have.
                var byAddress = !getter.IsStatic && getter.DeclaringType!.IsValueType;
                if (byAddress && !(i > 0 && PushesAddress(il[i - 1], method)))
                    continue;
                reads++;
                if (apply)
                {
                    instruction.OpCode = getter.IsStatic || byAddress ? CilOpCodes.Call : CilOpCodes.Callvirt;
                    instruction.Operand = getter;
                }
            }
        }
        return new Result(getters.Count, reads);
    }

    private static bool Within(TypeDefinition? type, TypeDefinition owner)
    {
        for (; type != null; type = type.DeclaringType)
            if (type == owner)
                return true;
        return false;
    }

    // Public non-virtual setters of classes that do nothing but store their value into a private field.
    private static Dictionary<FieldDefinition, MethodDefinition> ProvenSetters(ModuleDefinition module)
    {
        var setters = new Dictionary<FieldDefinition, MethodDefinition>();
        foreach (var property in module.GetAllTypes().SelectMany(t => t.Properties))
        {
            var setter = property.SetMethod;
            if (setter is not { IsPublic: true, IsVirtual: false, GenericParameters.Count: 0, CilMethodBody: { } body }
                || setter.IsPInvokeImpl || (setter.ImplAttributes & MethodImplAttributes.Synchronized) != 0
                || setter.Signature is not { ParameterTypes.Count: 1, ReturnType.ElementType: ElementType.Void }
                || setter.DeclaringType is not { IsValueType: false, GenericParameters.Count: 0 } owner
                || body.ExceptionHandlers.Count != 0)
                continue;
            var il = body.Instructions.Where(i => i.OpCode != CilOpCodes.Nop).ToList();
            il = il.Where((i, index) => !(i.OpCode == CilOpCodes.Br && i.Operand is CilInstructionLabel { Instruction: { } to }
                                          && index + 1 < il.Count && to == il[index + 1])).ToList();
            // The value parameter may be loaded in its long form, naming the parameter.
            var codes = il.Select(i => i.OpCode.Code is CilCode.Ldarg or CilCode.Ldarg_S && i.Operand is Parameter { Index: 0 }
                ? setter.IsStatic ? CilCode.Ldarg_0 : CilCode.Ldarg_1
                : i.OpCode.Code);
            var expected = setter.IsStatic
                ? new[] { CilCode.Ldarg_0, CilCode.Stsfld, CilCode.Ret }
                : new[] { CilCode.Ldarg_0, CilCode.Ldarg_1, CilCode.Stfld, CilCode.Ret };
            if (!codes.SequenceEqual(expected)
                || il[^2].Operand is not FieldDefinition field || field.DeclaringType != owner || field.DeclaringModule != module
                || field.IsStatic != setter.IsStatic || field.IsPublic || field.IsInitOnly
                || !SignatureComparer.Default.Equals(field.Signature!.FieldType, setter.Signature.ParameterTypes[0]))
                continue;
            setters.TryAdd(field, setter);
        }
        return setters;
    }

    private static bool PushesAddress(CilInstruction instruction, MethodDefinition method)
        => instruction.OpCode.Code is CilCode.Ldloca or CilCode.Ldloca_S or CilCode.Ldflda or CilCode.Ldarga or CilCode.Ldarga_S or CilCode.Ldsflda
           // a struct method's this is its address
           || instruction.OpCode.Code == CilCode.Ldarg_0 && !method.IsStatic && method.DeclaringType is { IsValueType: true };
}
