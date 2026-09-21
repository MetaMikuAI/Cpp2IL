using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Maps calls to KeyFunctionAddresses to their underlying IL opcodes. E.g. il2cpp_codegen_object_new => newobj.
/// Eventually will include box/unbox/throw/etc
/// </summary>
public static class KeyFunctionRecovery
{
    //All of these have the same params in the same order so we treat them as equal.
    private static readonly HashSet<string> ObjectNewFunctions =
    [
        "il2cpp_object_new",
        "il2cpp_vm_object_new",
        "il2cpp_codegen_object_new",
    ];

    //These all take the exception to throw as their only real argument.
    private static readonly HashSet<string> RaiseExceptionFunctions =
    [
        nameof(BaseKeyFunctionAddresses.il2cpp_raise_exception),
        nameof(BaseKeyFunctionAddresses.il2cpp_vm_exception_raise),
        nameof(BaseKeyFunctionAddresses.il2cpp_codegen_raise_exception),
    ];

    //Both take the class to box as and a pointer to the value.
    private static readonly HashSet<string> BoxFunctions =
    [
        nameof(BaseKeyFunctionAddresses.il2cpp_value_box),
        nameof(BaseKeyFunctionAddresses.il2cpp_vm_object_box),
    ];

    public static void Run(MethodAnalysisContext method)
    {
        ArrayElementClassRecovery.Run(method);
        var definitions = method.ControlFlowGraph!.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
        foreach (var instruction in method.ControlFlowGraph!.Blocks.SelectMany(block => block.Instructions))
        {
            if (TryRewriteIsInst(instruction, method, definitions) || TryRewriteBox(instruction, method)
                || ThreadStaticFieldRecovery.TryTypeLookup(instruction, method, definitions))
                continue;
            if (instruction.Operands is not [StringLiteral { Value: var keyFunction }, ..])
                continue;

            if (ObjectNewFunctions.Contains(keyFunction))
                RewriteObjectNew(instruction);
            else if (keyFunction == nameof(BaseKeyFunctionAddresses.il2cpp_codegen_write_barrier))
                RemoveWriteBarrier(instruction);
            else if (RaiseExceptionFunctions.Contains(keyFunction))
                RewriteRaiseException(instruction);
            else if (keyFunction == nameof(BaseKeyFunctionAddresses.il2cpp_vm_reflection_get_type_object))
                RewriteTypeObject(instruction);
            else if (keyFunction == nameof(BaseKeyFunctionAddresses.InternalCalls_Resolve))
                RewriteInternalCallResolve(instruction, method);
        }
    }

    private static bool TryRewriteIsInst(Instruction instruction, MethodAnalysisContext method,
        Dictionary<LocalVariable, Instruction> definitions)
    {
        if (instruction is not { OpCode: OpCode.Call, Operands: [var target, LocalVariable result, var value, var classOperand, ..] })
            return false;
        var seen = new HashSet<LocalVariable>();
        while (classOperand is LocalVariable local && seen.Add(local) && definitions.TryGetValue(local, out var definition)
            && definition is { OpCode: OpCode.Move or OpCode.Phi, Operands: [_, var source] })
            classOperand = source;
        // Require an actual metadata value, not a static type inferred for a dynamic
        // class pointer (or one arbitrarily chosen from a mixed phi).
        var castType = classOperand switch
        {
            RuntimeClassTypeAnalysisContext klass => klass.RepresentedType,
            TypeAnalysisContext { Type: Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_OBJECT
                or Il2CppTypeEnum.IL2CPP_TYPE_STRING or Il2CppTypeEnum.IL2CPP_TYPE_ARRAY
                or Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY or Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST
                or Il2CppTypeEnum.IL2CPP_TYPE_VAR or Il2CppTypeEnum.IL2CPP_TYPE_MVAR } type => type,
            _ => null
        };
        if (castType == null || castType.IsValueType
            || castType is GenericParameterTypeAnalysisContext generic && !HasReferenceTypeConstraint(generic))
            return false;
        if (target is not StringLiteral { Value: nameof(BaseKeyFunctionAddresses.il2cpp_vm_object_is_inst) })
        {
            if (target is not Immediate address) return false;
            var known = method.AppContext.GetOrCreateKeyFunctionAddresses().il2cpp_vm_object_is_inst;
            if (known == 0 || address.UnsignedValue != known
                && (method.AppContext.InstructionSet is not InstructionSets.NewArmV8InstructionSet
                    || NewArm64KeyFunctionAddresses.GetBranchThunkTarget(method.AppContext, address.UnsignedValue) != known))
                return false;
        }
        result.Type = castType;
        instruction.OpCode = OpCode.TryCast;
        instruction.SetOperands(result, castType, value);
        return true;
    }

    private static bool HasReferenceTypeConstraint(GenericParameterTypeAnalysisContext type)
    {
        // TryCast stores the returned object directly as T; value-type T would need unboxing.
        // Interfaces and Object/ValueType/Enum constraints do not rule out value types.
        if ((type.Attributes & System.Reflection.GenericParameterAttributes.NotNullableValueTypeConstraint) != 0)
            return false;
        return (type.Attributes & System.Reflection.GenericParameterAttributes.ReferenceTypeConstraint) != 0
            || type.ConstraintTypes.Any(constraint => constraint is not GenericParameterTypeAnalysisContext
                && constraint.Type is Il2CppTypeEnum.IL2CPP_TYPE_CLASS or Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST
                && !constraint.IsInterface && !constraint.IsValueType
                && !(constraint.Namespace == "System" && constraint.Name is "Object" or "ValueType" or "Enum"));
    }

    private static void RemoveWriteBarrier(Instruction instruction)
    {
        instruction.OpCode = OpCode.Nop;
        instruction.SetOperands();
    }
    
    private static void RewriteRaiseException(Instruction instruction)
    {
        // A void call has no return value operand, so the exception is one slot earlier
        var exceptionIndex = instruction.OpCode == OpCode.CallVoid ? 1 : 2;

        if (!instruction.IsCall || instruction.Operands.Count <= exceptionIndex)
            return;

        var exception = instruction.Operands[exceptionIndex];

        instruction.OpCode = OpCode.Throw;
        instruction.SetOperands(exception);
    }

    private static bool TryRewriteBox(Instruction instruction, MethodAnalysisContext method)
    {
        // function name, result, class, address of value.
        if (instruction.OpCode != OpCode.Call || instruction.Operands is not [var target, var result, TypeAnalysisContext boxedType, var value, ..])
            return false;

        if (target is not StringLiteral name || !BoxFunctions.Contains(name.Value))
        {
            // Codegen may use a sibling of the exported boxing thunk. Follow only
            // an entry-point B: calls or argument-adjusting wrappers are not equivalent.
            if (target is not Immediate address || method.AppContext.InstructionSet is not InstructionSets.NewArmV8InstructionSet
                || !boxedType.IsValueType
                || value is not AddressOf { Target: LocalVariable valueLocal }
                || valueLocal.Type != null && valueLocal.Type != boxedType)
                return false;
            var implementation = NewArm64KeyFunctionAddresses.GetBranchThunkTarget(method.AppContext, address.UnsignedValue);
            if (implementation == 0)
                return false;
            var known = method.AppContext.GetOrCreateKeyFunctionAddresses();
            if (implementation != known.il2cpp_value_box && implementation != known.il2cpp_vm_object_box)
                return false;
            // The proven boxing helper and its class argument establish the pointee type.
            // Do this only after verifying the target, and never overwrite a conflicting type.
            valueLocal.Type ??= boxedType;
        }

        instruction.OpCode = OpCode.Box;
        instruction.SetOperands(result, boxedType, value);
        return true;
    }

    private static void RewriteTypeObject(Instruction instruction)
    {
        if (instruction.OpCode != OpCode.Call || instruction.Operands is not [_, var result, TypeAnalysisContext type, ..])
            return;

        instruction.OpCode = OpCode.Move;
        instruction.SetOperands(result, type);
    }

    private static void RewriteInternalCallResolve(Instruction instruction, MethodAnalysisContext method)
    {
        if (instruction.OpCode != OpCode.Call || instruction.Operands is not [_, var result, Immediate nameAddress, ..])
            return;

        if (ThrowHelperRecovery.ReadCStringAtVirtualAddress(method.AppContext, nameAddress.UnsignedValue, 256) is not { } name)
            return;

        if (ResolveInternalCallName(method.AppContext, name) is not { DeclaringType.DeclaringAssembly: { } assembly } resolved)
            return;

        var pointer = new RuntimeMethodInfoAnalysisContext(resolved, assembly);

        instruction.OpCode = OpCode.Move;
        instruction.SetOperands(result, pointer);

        RewriteCachedPointerLoads(method, result, pointer);
    }

    private static void RewriteCachedPointerLoads(MethodAnalysisContext method, IOperand result, RuntimeMethodInfoAnalysisContext pointer)
    {
        var cache = method.ControlFlowGraph!.Instructions
            .Where(i => i is { OpCode: OpCode.Move, Operands: [MemoryOperand { IsConstant: true }, _] })
            .Where(i => ReferenceEquals(i.Operands[1], result))
            .Select(i => ((MemoryOperand)i.Operands[0]).Addend)
            .Distinct()
            .ToList();

        if (cache.Count != 1)
            return;

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable destination, MemoryOperand { IsConstant: true } load] }
                && load.Addend == cache[0])
                instruction.SetOperands(destination, pointer);
        }
    }

    internal static MethodAnalysisContext? ResolveInternalCallName(ApplicationAnalysisContext appContext, string name)
    {
        var separator = name.IndexOf("::", StringComparison.Ordinal);

        if (separator < 0)
            return null;

        var typeName = name[..separator];
        var signature = name[(separator + 2)..];
        var parenthesis = signature.IndexOf('(');
        var methodName = parenthesis < 0 ? signature : signature[..parenthesis];

        if (appContext.LibCpp2IlContext.ReflectionCache.GetTypeByFullName(typeName) is not { } typeDefinition
            || appContext.ResolveContextForType(typeDefinition) is not { } type)
            return null;

        var candidates = type.Methods.Where(m => m.Name == methodName).ToList();

        if (candidates.Count <= 1)
            return candidates.FirstOrDefault();

        // Overloaded, so fall back on the parameter list in the name
        var parameters = parenthesis < 0 ? "" : signature[(parenthesis + 1)..].TrimEnd(')');
        var count = parameters.Length == 0 ? 0 : parameters.Split(',').Length;

        var byParameterCount = candidates.Where(m => m.Parameters.Count == count).ToList();

        return byParameterCount.Count == 1 ? byParameterCount[0] : null;
    }

    private static void RewriteObjectNew(Instruction instruction)
    {
        // Needs the function name, the result, and the class argument.
        if (instruction.OpCode != OpCode.Call || instruction.Operands.Count < 3)
            return;

        var result = instruction.Operands[1];
        var klass = instruction.Operands[2];

        instruction.OpCode = OpCode.Newobj;
        instruction.SetOperands(result, klass);
    }
}
