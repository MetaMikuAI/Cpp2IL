using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

public static class LocalVariables
{
    public static int MaxTypePropagationLoopCount = 5000;

    private const long StaticFieldsOffset64 = 0xB8;
    private const long StaticFieldsOffset32 = 0x5C;

    public static void CreateAll(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        var instructions = cfg.Instructions;

        // Get all registers
        var registers = new List<Register>();
        foreach (var instruction in instructions)
            registers.AddRange(GetRegisters(instruction));

        // Remove duplicates
        registers = registers.Distinct().ToList();

        // Map those to locals
        var locals = new Dictionary<Register, LocalVariable>();
        for (var i = 0; i < registers.Count; i++)
        {
            var register = registers[i];
            locals.Add(register, new LocalVariable($"v{i}", register,
                method.StackAggregates.GetValueOrDefault(register.Number)));
        }

        // Replace registers with locals
        foreach (var instruction in instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                var operand = instruction.Operands[i];

                if (operand is Register register)
                    instruction.SetOperand(i, locals[register]);

                if (operand is AddressOf { Target: Register addressed })
                    instruction.SetOperand(i, new AddressOf(locals[addressed]));

                if (operand is MemoryOperand memory)
                {
                    if (memory.Base != null)
                    {
                        var baseRegister = (Register)memory.Base;
                        memory.Base = locals[baseRegister];
                    }

                    if (memory.Index != null)
                    {
                        var index = (Register)memory.Index;
                        memory.Index = locals[index];
                    }

                    instruction.SetOperand(i, memory);
                }
            }
        }

        method.Locals = locals.Select(kv => kv.Value).ToList();
        StackAggregateRecovery.ResolveFields(method);

        // Return local names
        var retValIndex = 0;
        foreach (var instruction in instructions)
        {
            if (instruction.OpCode != OpCode.Return || instruction.Operands.Count != 1) continue;

            var returnLocal = (LocalVariable)instruction.Sources[0];

            returnLocal.Name = $"returnVal{retValIndex + 1}";
            returnLocal.IsReturn = true;
            retValIndex++;
        }

        // Add parameter names
        var paramLocals = new List<LocalVariable>();

        var operandOffset = method.IsStatic ? 0 : 1; // 'this'

        // 'this' param
        if (!method.IsStatic && method.Locals.Count > 0 && method.ParameterOperands.Count > 0)
        {
            var thisOperand = (Register)method.ParameterOperands[0];
            var thisLocal = method.Locals.FirstOrDefault(l => l.Register.Number == thisOperand.Number && l.Register.Version == -1);

            if (thisLocal != null)
            {
                thisLocal.Name = "this";
                thisLocal.IsThis = true;
                paramLocals.Add(thisLocal);
            }
            else
            {
                method.AddWarning($"'this' local not found (operand: {thisOperand})");
            }
        }

        // Check if method has MethodInfo*
        var hasMethodInfo = (method.ParameterOperands.Count - operandOffset) > method.Parameters.Count;
        var methodInfoIndex = method.ParameterOperands.Count - 1;

        // Add normal parameter names
        for (var i = 0; i < method.Parameters.Count; i++)
        {
            var operandIndex = i + operandOffset;
            if (hasMethodInfo && operandIndex == methodInfoIndex)
                break; // Skip MethodInfo*

            if (operandIndex >= method.ParameterOperands.Count)
                break;

            if (method.ParameterOperands[operandIndex] is not Register reg)
                continue;

            var local = method.Locals.FirstOrDefault(l => l.Register.Number == reg.Number && l.Register.Version == -1);
            if (local == null)
                continue;

            local.Name = method.Parameters[i].ParameterName;
            paramLocals.Add(local);
        }

        // Add MethodInfo*
        if (hasMethodInfo)
        {
            var methodInfoOperand = (Register)method.ParameterOperands[methodInfoIndex];
            var methodInfoLocal = method.Locals.FirstOrDefault(l => l.Register.Number == methodInfoOperand.Number && l.Register.Version == -1);

            if (methodInfoLocal != null)
            {
                methodInfoLocal.Name = "methodInfo";
                methodInfoLocal.IsMethodInfo = true;
                paramLocals.Add(methodInfoLocal);
            }
        }

        method.ParameterLocals = paramLocals;

        // the hidden return buffer takes the first argument register. we type it as the return
        // type so stores into it resolve to fields
        if (method.AppContext.Binary.PointerSizeBytes == 8
            && method.AppContext.InstructionSet.CallingConventionResolver?.HiddenReturnBufferRegister(method) is { } bufferRegister
            && method.Locals.FirstOrDefault(l => l.Register.Number == bufferRegister.Number && l.Register.Version == -1) is { } bufferLocal)
        {
            bufferLocal.Name = "returnBuffer";
            bufferLocal.Type = method.ReturnType;
        }
    }

    public static void RemoveUnused(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        cfg.BuildUseDefLists();

        var usedLocals = new HashSet<LocalVariable>();

        foreach (var block in cfg.Blocks)
        {
            foreach (var usedVar in block.Use.OfType<LocalVariable>())
                usedLocals.Add(usedVar);

            foreach (var definedVar in block.Def.OfType<LocalVariable>())
                usedLocals.Add(definedVar);
        }

        method.Locals.RemoveAll(x => !usedLocals.Contains(x));
    }

    private static List<Register> GetRegisters(Instruction instruction)
    {
        var registers = new List<Register>();

        if (instruction.ImplicitDefinition is { } implicitDefinition)
            registers.Add(implicitDefinition);

        foreach (var operand in instruction.Operands)
        {
            if (operand is AddressOf { Target: Register addressed })
            {
                if (!registers.Contains(addressed))
                    registers.Add(addressed);
            }

            if (operand is Register register)
            {
                if (!registers.Contains(register))
                    registers.Add(register);
            }

            if (operand is MemoryOperand memory)
            {
                if (memory.Base != null)
                {
                    var baseRegister = (Register)memory.Base;
                    if (!registers.Contains(baseRegister))
                        registers.Add(baseRegister);
                }

                if (memory.Index != null)
                {
                    var index = (Register)memory.Index;
                    if (!registers.Contains(index))
                        registers.Add(index);
                }
            }
        }

        return registers;
    }

    /// <summary>
    /// Resolves field accesses and propagates types together, to a fixpoint, while the method is
    /// still in SSA form (every local has a single, version-stable definition).
    ///
    /// The two are mutually enabling and so cannot be ordered as separate passes: a typed base lets
    /// <see cref="MetadataResolver.ResolveFieldOffsets"/> turn <c>[base + offset]</c> into a
    /// <see cref="FieldReference"/>, a resolved field load types its result with the field's type,
    /// and that result is in turn the base of the next access (directly, or after flowing through
    /// moves/phis). Both steps are monotonic - each only ever resolves an operand or fills a
    /// previously-unknown type - so the loop converges.
    /// </summary>
    public static void ResolveTypesAndFields(MethodAnalysisContext method)
    {
        // Seed types from fixed ground truth - the method's own signature, and type-metadata global
        // loads. Applied once up front and, being applied first, they win over anything inferred later.
        PropagateFromReturn(method);
        PropagateFromParameters(method);
        SeedRuntimeClassTypes(method);
        SeedNewobjResults(method);
        SeedMethodInfoTypes(method);
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction is { OpCode: OpCode.MultiplyHighSigned, Destination: LocalVariable product })
                product.Type = method.AppContext.SystemTypes.SystemInt64Type;
            // localloc yields an unmanaged pointer to raw stack bytes.
            if (instruction is { OpCode: OpCode.LocalAllocate, Destination: LocalVariable allocated })
            {
                allocated.Type = method.AppContext.SystemTypes.SystemByteType.MakePointerType();
                if (instruction.Operands[1] is LocalVariable { Type: null } size)
                    size.Type = method.AppContext.SystemTypes.SystemUInt64Type;
            }
            if (instruction is { OpCode: OpCode.ConvertNumeric,
                Operands: [LocalVariable converted, _, NumericConversion conversion] })
                converted.Type = conversion.TargetType;
            if (instruction is { OpCode: OpCode.SignExtend,
                Operands: [_, LocalVariable { Type: null } source, Immediate { Value: 32 }] })
                source.Type = method.AppContext.SystemTypes.SystemInt32Type;
            if (instruction is { OpCode: OpCode.ZeroExtend or OpCode.SignExtend, Destination: LocalVariable extended })
                extended.Type = instruction.OpCode == OpCode.SignExtend
                    ? method.AppContext.SystemTypes.SystemInt64Type : method.AppContext.SystemTypes.SystemUInt64Type;
            if (instruction is { OpCode: OpCode.ShiftLeft or OpCode.ShiftRight,
                Operands: [LocalVariable shifted, _, _, TypeAnalysisContext shiftType] })
                shifted.Type = shiftType;
        }

        SeedComparisonResults(method);
        SeedFloatLiterals(method);

        // Everything else is mutually enabling and so runs to a fixpoint: a typed receiver lets an
        // ambiguous call resolve, a resolved call types its return value and arguments, a typed base
        // lets a field offset resolve, a field load types its result, and any of those can be the
        // receiver/base of the next step. Every pass is monotonic - it only resolves an operand or
        // fills a previously-unknown type - so the loop converges.
        var changed = true;
        var loopCount = 0;

        while (changed)
        {
            if (MaxTypePropagationLoopCount != -1 && ++loopCount > MaxTypePropagationLoopCount)
                throw new DecompilerException($"Type and field resolution not settling! (looped {MaxTypePropagationLoopCount} times)");

            changed = false;
            changed |= NativeMethodCloneRecovery.Run(method);
            changed |= MetadataResolver.ResolveCallsViaMethodInfo(method);
            changed |= MetadataResolver.ResolveAmbiguousCalls(method);
            // The allocation type may only become known during this fixpoint.
            changed |= MetadataResolver.ResolveConstructorCalls(method);
            changed |= MetadataResolver.ResolveVirtualCalls(method);
            // Copies and phis carry a definition's type before a call's receiver is typed from the callee,
            // whose declaring type may be only a base class of the copied local (e.g. of 'this').
            changed |= PropagateCopiesOnce(method);
            changed |= PropagateFromCallParameters(method);
            changed |= AggregateCopyRecovery.Run(method);
            changed |= MetadataResolver.ResolveFieldOffsets(method, deferUntypedStores: true);
            changed |= RefineObjectFieldLoads(method);
            changed |= RgctxResolver.Run(method);
            changed |= RecoverPackedMembers(method);
            changed |= RecoverMemberAddresses(method);
            changed |= PropagateStaticFieldStorage(method);
            changed |= TypeAddressedLocals(method);
            changed |= PropagateTypesOnce(method);
        }

        // Stores deferred for their value's type that never came get resolved as they would have been.
        if (MetadataResolver.ResolveFieldOffsets(method))
            PropagateTypesOnce(method);
    }

    // A call taking object constrains assignability, not the actual type of a field load.
    // Refine only single-definition loads while still in SSA; never narrow phi/merged values.
    private static bool RefineObjectFieldLoads(MethodAnalysisContext method)
    {
        var instructions = method.ControlFlowGraph!.Instructions;
        var definitions = instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).ToDictionary(g => g.Key, g => g.Count());
        var changed = false;
        foreach (var instruction in instructions)
        {
            if (instruction is not { OpCode: OpCode.Move,
                Operands: [LocalVariable destination, FieldReference field] }
                || destination.Type != method.AppContext.SystemTypes.SystemObjectType
                || definitions[destination] != 1
                || field.Field.FieldType is not { IsValueType: false } type
                || type == destination.Type
                || type is PointerTypeAnalysisContext or ByRefTypeAnalysisContext or GenericParameterTypeAnalysisContext)
                continue;
            destination.Type = type;
            changed = true;
        }
        return changed;
    }

    /// <summary>
    /// A value type no wider than a register travels packed in one general register, and native code
    /// reads its 32-bit halves with integer operations: <c>lsr x, x, #32</c> for the member at offset 4,
    /// <c>and x, x, #0xFFFFFFFF</c> for the member at offset 0. Each is a read of that member, so the
    /// operation is rewritten to load it, keeping the extension the native operation applied. Only an
    /// unambiguous 32-bit member qualifies (a sequential struct with exactly one member covering those
    /// four bytes); anything else stays as is. Rewriting is one-way, so the fixpoint still converges.
    /// </summary>
    internal static bool RecoverPackedMembers(MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        if (pointerSize != 8)
            return false;

        var types = method.AppContext.SystemTypes;
        var changed = false;
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            // The explicit type, when present, says whether the native shift was logical or arithmetic.
            var (destination, source, offset, extension) = instruction switch
            {
                { OpCode: OpCode.ShiftRight, Operands: [LocalVariable d, LocalVariable s, Immediate { Value: 32 }] }
                    => (d, s, 4, (OpCode?)null),
                { OpCode: OpCode.ShiftRight, Operands: [LocalVariable d, LocalVariable s, Immediate { Value: 32 }, TypeAnalysisContext t] }
                    when t == types.SystemInt64Type || t == types.SystemUInt64Type
                    => (d, s, 4, t == types.SystemInt64Type ? OpCode.SignExtend : OpCode.ZeroExtend),
                { OpCode: OpCode.And, Operands: [LocalVariable d, LocalVariable s, Immediate { Value: 0xFFFFFFFF }] }
                    => (d, s, 0, OpCode.ZeroExtend),
                _ => (null, null, 0, null),
            };

            if (destination == null || source?.Type is not { } packed || PackedMember(packed, offset, pointerSize) is not { } member)
                continue;

            var memberType = member.FieldType.IsEnumType ? member.FieldType.EnumUnderlyingType : member.FieldType;
            var integer = memberType?.FullName is "System.Int32" or "System.UInt32";
            if (!integer && (extension != null || memberType?.FullName != "System.Single"))
                continue;

            var read = new FieldReference(member, source, offset);
            if (extension is { } opCode)
            {
                instruction.OpCode = opCode;
                instruction.SetOperands(destination, read, new Immediate(32));
            }
            else
            {
                instruction.OpCode = OpCode.Move;
                instruction.SetOperands(destination, read);
            }

            changed = true;
        }

        return changed;
    }

    /// <summary>
    /// <c>base + K</c>, where the base is the address of a typed struct's storage (a frame slot's
    /// address or a managed pointer) or a typed object, and exactly one instance member starts at
    /// offset K, computes that member's address: ldflda, not integer arithmetic on a pointer.
    ///
    /// Recovered only where every use consumes the value as an address that stays inside the member:
    /// a call argument, or (for struct storage) a memory access within the member's extent. An object
    /// base's accesses are left alone, since field resolution already follows <c>obj + K</c> into
    /// accesses that may reach past the member.
    ///
    /// The receiver must be a value the method never assigns (a parameter, including <c>this</c>):
    /// copy forwarding, coalescing and dead-copy removal track a field's receiver as a plain operand
    /// but not inside an address-of, so a receiver defined in the method could lose its definition.
    /// </summary>
    internal static bool RecoverMemberAddresses(MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var instructions = method.ControlFlowGraph!.Instructions;
        var changed = false;

        // A number stored into a struct local that fits its first member is a store to that member, which
        // is how a frame slot holding a struct receives one (an async state machine's <>1__state = -1). A
        // wider one packs several members (Vector2Int (1, 1) as 0x100000001) and a zero clears the whole
        // value; both are left as they are.
        foreach (var instruction in instructions)
            if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable { Type: { Type: Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE, IsEnumType: false } structType } storage, Immediate { Value: not 0 } number] }
                && SoleMemberAt(structType, 0, false) is { FieldType: { } memberType } first
                && memberType.Namespace == "System"
                && memberType.Name switch
                {
                    "Int64" or "UInt64" => true,
                    "Int32" or "UInt32" => number.Value is >= int.MinValue and <= uint.MaxValue,
                    "Int16" or "UInt16" => number.Value is >= short.MinValue and <= ushort.MaxValue,
                    "Byte" or "SByte" or "Boolean" => number.Value is >= sbyte.MinValue and <= byte.MaxValue,
                    _ => false
                })
            {
                instruction.SetOperand(0, new FieldReference(first, storage, 0));
                changed = true;
            }

        var assigned = instructions.Select(i => i.Destination).OfType<LocalVariable>().ToHashSet();
        foreach (var instruction in instructions)
        {
            if (instruction is not { OpCode: OpCode.Add, Operands: [LocalVariable destination, var left, var right] }
                || destination.Type is not (null or ByRefTypeAnalysisContext))
                continue;
            if (left is Immediate)
                (left, right) = (right, left);
            if (right is not Immediate { Value: > 0 and <= int.MaxValue } offset)
                continue;

            LocalVariable? receiver = null;
            TypeAnalysisContext? owner = null;
            var isObject = false;
            switch (left)
            {
                case AddressOf { Target: LocalVariable { Type: { IsValueType: true } storageType } storage }
                    when storageType is not ByRefTypeAnalysisContext:
                    (receiver, owner) = (storage, storageType);
                    break;
                case LocalVariable { Type: ByRefTypeAnalysisContext { ElementType: { IsValueType: true } referent } } pointer:
                    (receiver, owner) = (pointer, referent);
                    break;
                case LocalVariable { Type: { IsValueType: false } instanceType } instance when IsPlainClass(instanceType, method):
                    (receiver, owner, isObject) = (instance, instanceType, true);
                    break;
            }

            if (receiver == null || owner == null || assigned.Contains(receiver)
                || SoleMemberAt(owner, offset.Value, isObject) is not { } member)
                continue;

            // A managed pointer the call signatures already typed must agree with the member.
            if (destination.Type is ByRefTypeAnalysisContext { ElementType: var typed }
                && (typed.FullName != member.FieldType.FullName || typed.DeclaringAssembly != member.FieldType.DeclaringAssembly))
                continue;

            var extent = MemberSize(member.FieldType, pointerSize);
            if (extent <= 0 || !UsedOnlyAsMemberAddress(destination, instructions, extent, allowAccesses: !isObject))
                continue;

            instruction.OpCode = OpCode.Move;
            instruction.SetOperands(destination, new AddressOf(new FieldReference(member, receiver, (int)offset.Value)));
            destination.Type = new ByRefTypeAnalysisContext(member.FieldType);
            changed = true;
        }

        return changed;
    }

    // An ordinary class whose metadata offsets are real: not a generic (placeholder offsets), not a
    // runtime-synthesized handle, and not string, whose trailing characters are not a single member.
    private static bool IsPlainClass(TypeAnalysisContext type, MethodAnalysisContext method) =>
        type is not (RuntimeClassTypeAnalysisContext or StaticFieldStorageTypeAnalysisContext or RuntimeMethodInfoAnalysisContext
            or RuntimeFieldInfoAnalysisContext or PointerTypeAnalysisContext or SzArrayTypeAnalysisContext
            or GenericInstanceTypeAnalysisContext or GenericParameterTypeAnalysisContext)
        && type != method.AppContext.SystemTypes.SystemStringType
        && type.GenericParameters.Count == 0;

    private static FieldAnalysisContext? SoleMemberAt(TypeAnalysisContext owner, long offset, bool searchBases)
    {
        for (var type = owner; type != null; type = searchBases ? type.BaseType : null)
        {
            if (type.GenericParameters.Count != 0 || type is GenericInstanceTypeAnalysisContext
                || (type.Attributes & System.Reflection.TypeAttributes.ExplicitLayout) != 0)
                return null;
            var members = type.Fields.Where(f => !f.IsStatic && f.Offset == offset
                && (f.Attributes & System.Reflection.FieldAttributes.Literal) == 0).ToList();
            if (members.Count > 0)
                return members is [{ } member] ? member : null;
        }

        return null;
    }

    private static bool UsedOnlyAsMemberAddress(LocalVariable address, List<Instruction> instructions, long extent, bool allowAccesses)
    {
        var used = false;
        foreach (var instruction in instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                var operand = instruction.Operands[i];
                if (ReferenceEquals(operand, address))
                {
                    // Writing the address itself (it is the definition) is fine; any other plain use must
                    // be a call argument, where the signature decides how the address is consumed.
                    if (i == 0 && ReferenceEquals(instruction.Destination, address))
                        continue;
                    var firstArgument = instruction.OpCode == OpCode.CallVoid ? 1 : 2;
                    if (!instruction.IsCall || i < firstArgument)
                        return false;
                    used = true;
                    continue;
                }

                if (operand is MemoryOperand memory && (ReferenceEquals(memory.Base, address) || ReferenceEquals(memory.Index, address)))
                {
                    if (!allowAccesses || !ReferenceEquals(memory.Base, address) || memory.Index != null
                        || memory.Addend < 0 || memory.AccessSize <= 0 || memory.Addend + memory.AccessSize > extent)
                        return false;
                    used = true;
                }
                else if (operand is AddressOf { Target: var target } && ReferenceEquals(target, address))
                    return false;
            }
        }

        return used;
    }

    private static FieldAnalysisContext? PackedMember(TypeAnalysisContext type, int offset, int pointerSize)
    {
        if (type is not { IsValueType: true, IsEnumType: false } or ByRefTypeAnalysisContext
            || type.Type != LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE
            || type.GenericParameters.Count != 0
            || (type.Attributes & System.Reflection.TypeAttributes.ExplicitLayout) != 0
            || TypeSizes.UnboxedSize(type, pointerSize) != pointerSize)
            return null;

        var covering = type.Fields.Where(f => !f.IsStatic && f.Offset <= offset
            && f.Offset + MemberSize(f.FieldType, pointerSize) > offset).ToList();
        return covering is [{ } member] && member.Offset == offset
            && MemberSize(member.FieldType, pointerSize) == 4 ? member : null;
    }

    private static long MemberSize(TypeAnalysisContext type, int pointerSize) =>
        type.IsValueType ? TypeSizes.UnboxedSize(type, pointerSize) : pointerSize;

    // A type-metadata global load (Move local, typeof(T)) puts the runtime class pointer for T into
    // the local - an Il2CppClass*, not an instance of T. That is known exactly from the instruction,
    // so it is seeded as ground truth (overriding any prior guess) before the inference fixpoint,
    // rather than letting a monotonic pass first mistype the local as T itself.
    private static void SeedRuntimeClassTypes(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Move || instruction.Operands.Count < 2)
                continue;

            if (instruction.Operands[0] is LocalVariable destination
                && instruction.Operands[1] is TypeAnalysisContext type and not (RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext))
                destination.Type = new RuntimeClassTypeAnalysisContext(type, type.DeclaringAssembly);
        }
    }

    private static void SeedNewobjResults(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Newobj || instruction.Operands.Count < 2)
                continue;

            if (instruction.Operands[0] is LocalVariable destination && InstantiatedType(instruction.Operands[1]) is { } type)
                destination.Type = type;
        }
    }

    private static TypeAnalysisContext? InstantiatedType(IOperand classOperand) =>
        classOperand switch
        {
            LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: var t } } => t,
            RuntimeClassTypeAnalysisContext { RepresentedType: var t } => t,
            TypeAnalysisContext type => type, //not sure this is actually valid but for completeness
            _ => null,
        };

    // A method/field-metadata global load (Move local, methodof(M) / fieldof(F)) puts a MethodInfo*
    // or FieldInfo* into the local. MetadataResolver already resolved the address to a context naming
    // the member; that same context is the local's type (a runtime handle, recoverable via its
    // RepresentedMethod/RepresentedField).
    private static void SeedMethodInfoTypes(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Move || instruction.Operands.Count < 2)
                continue;

            if (instruction.Operands[0] is LocalVariable destination
                && instruction.Operands[1] is RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext)
                destination.Type = (TypeAnalysisContext)instruction.Operands[1];
        }
    }

    // A comparison (CheckEqual, CheckLess, ...) writes a 0/1 result into its destination, so that local
    // is a System.Boolean regardless of what the compared operands are.
    private static void SeedComparisonResults(MethodAnalysisContext method)
    {
        var booleanType = method.AppContext.SystemTypes.SystemBooleanType;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode is < OpCode.CheckEqual or > OpCode.CheckLessOrEqual)
                continue;

            if (instruction.Destination is LocalVariable destination)
                destination.Type = booleanType;
        }
    }
    
    //Handles typing of locals for ref/out params. Returns whether anything new was typed
    public static bool TypeAddressedLocals(MethodAnalysisContext method)
    {
        var changed = false;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (!instruction.IsCall || instruction.Operands[0] is not MethodAnalysisContext calledMethod)
                continue;

            var firstArg = instruction.OpCode == OpCode.CallVoid ? 1 : 2;

            // the receiver of a value type's instance method is a pointer to the value
            if (!calledMethod.IsStatic && firstArg < instruction.Operands.Count
                && instruction.Operands[firstArg] is AddressOf { Target: LocalVariable receiver }
                && calledMethod.DeclaringType is { IsValueType: true } declaringType)
                changed |= SetTypeIfUnknown(receiver, declaringType);

            var paramOffset = firstArg + (calledMethod.IsStatic ? 0 : 1);

            for (var i = paramOffset; i < instruction.Operands.Count; i++)
            {
                var parameterIndex = i - paramOffset;
                if (parameterIndex > calledMethod.Parameters.Count - 1) // Probably MethodInfo*
                    continue;

                if (instruction.Operands[i] is AddressOf { Target: LocalVariable referenced }
                    && calledMethod.Parameters[parameterIndex].ParameterType is ByRefTypeAnalysisContext { ElementType: { } referencedType })
                    changed |= SetTypeIfUnknown(referenced, referencedType);
            }
        }

        return changed;
    }

    // Fills in a local's type only when it is currently unknown, keeping propagation monotonic (a
    // type, once set, is never changed) so the fixpoint terminates. Returns whether it set anything.
    private static bool SetTypeIfUnknown(LocalVariable local, TypeAnalysisContext? type)
    {
        if (type == null || local.Type != null)
            return false;

        local.Type = type;
        return true;
    }

    private static bool PropagateStaticFieldStorage(MethodAnalysisContext method)
    {
        var staticFieldsOffset = method.AppContext.Binary.is32Bit ? StaticFieldsOffset32 : StaticFieldsOffset64;
        var changed = false;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Move || instruction.Operands.Count < 2)
                continue;

            if (instruction.Operands[0] is not LocalVariable destination || destination.Type is StaticFieldStorageTypeAnalysisContext)
                continue;

            if (instruction.Operands[1] is not MemoryOperand { Index: null, Scale: 0 } memory || memory.Addend != staticFieldsOffset)
                continue;

            if (memory.Base is not LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: var owner } })
                continue;

            destination.Type = new StaticFieldStorageTypeAnalysisContext(owner, owner.DeclaringAssembly);
            changed = true;
        }

        return changed;
    }

    // Late recoveries introduce typed values after metadata resolution has finished.
    // Propagate only those known types; do not rerun metadata or native-layout rewrites.
    internal static void PropagateKnownTypes(MethodAnalysisContext method)
    {
        bool changed;
        do
        {
            changed = false;
            // Seed bool/literal operations only after field and array recovery has established
            // storage/index types. Early backward phi propagation can otherwise mistype those uses.
            foreach (var instruction in method.ControlFlowGraph!.Instructions)
                if (instruction is { OpCode: OpCode.And or OpCode.Or or OpCode.Xor,
                        Operands: [LocalVariable destination, var left, var right] }
                    && ((IsBoolean(left, method) && right is Immediate { Value: 0 or 1 })
                        || (left is Immediate { Value: 0 or 1 } && IsBoolean(right, method))))
                    changed |= SetTypeIfUnknown(destination, method.AppContext.SystemTypes.SystemBooleanType);
            changed |= PropagateTypesOnce(method);
        } while (changed);
    }

    // Only copies of class-typed parameters ('this' above all), directly or through such copies: a value
    // type or interface may be just what a register holds of a larger value (the first member of a struct
    // passed in two registers), and typing other copies ahead of the usual order upsets later passes.
    private static bool PropagateCopiesOnce(MethodAnalysisContext method)
    {
        var sources = new HashSet<LocalVariable>(method.ParameterLocals);
        var changed = false;
        for (var grown = true; grown;)
        {
            grown = false;
            foreach (var instruction in method.ControlFlowGraph!.Instructions)
                if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable { Type: null } copy, LocalVariable { Type: { IsValueType: false, IsInterface: false } type } source] }
                    && sources.Contains(source)
                    && type is not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext or GenericParameterTypeAnalysisContext)
                    && SetTypeIfUnknown(copy, type))
                {
                    sources.Add(copy);
                    grown = changed = true;
                }
        }
        return changed;
    }

    // A single propagation sweep over every move and phi. Returns whether it filled in any type.
    private static bool PropagateTypesOnce(MethodAnalysisContext method)
    {
        var changed = false;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            switch (instruction.OpCode)
            {
                case OpCode.Move:
                    changed |= PropagateMove(instruction, method.AppContext.Binary.PointerSizeBytes);
                    break;
                case OpCode.Phi:
                    changed |= PropagatePhi(instruction);
                    break;
                case OpCode.Box:
                    // Boxing metadata proves the addressed payload type, not the
                    // reference type of the boxed result or its native address.
                    if (instruction.Operands is [_, TypeAnalysisContext { IsValueType: true } boxedType,
                        AddressOf { Target: LocalVariable payload }])
                        changed |= SetTypeIfUnknown(payload, boxedType);
                    break;
                case OpCode.Add or OpCode.Subtract or OpCode.Multiply:
                    changed |= PropagateArithmetic(instruction, method) || PropagateKnownIntegerArithmetic(instruction, method);
                    break;
                case OpCode.Divide or OpCode.Modulo:
                    changed |= PropagateArithmetic(instruction, method) || PropagateIntegerResult(instruction, method);
                    break;
                case OpCode.And or OpCode.Or or OpCode.Xor or OpCode.Not or OpCode.Negate
                    or OpCode.ShiftLeft or OpCode.ShiftRight:
                    changed |= PropagateBooleanResult(instruction, method);
                    changed |= instruction.OpCode is (OpCode.And or OpCode.Or or OpCode.Xor)
                        && PropagateKnownIntegerArithmetic(instruction, method);
                    changed |= PropagateIntegerResult(instruction, method);
                    break;
            }
        }

        return PropagateIntegerRecurrences(method) | changed;
    }

    // Break a closed integer recurrence's type cycle: sum = phi(0, sum + intValue).
    // The typed step supplies the width; an untyped literal alone must never do so.
    internal static bool PropagateIntegerRecurrences(MethodAnalysisContext method)
    {
        var instructions = method.ControlFlowGraph!.Instructions;
        var phis = instructions.Where(i => i is { OpCode: OpCode.Phi, Destination: LocalVariable { Type: null } }).ToList();
        if (phis.Count == 0) return false;
        var definitions = instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());
        IOperand Value(IOperand value)
        {
            var seen = new HashSet<LocalVariable>();
            while (value is LocalVariable local && seen.Add(local) && definitions.TryGetValue(local, out var definition)
                && definition is { OpCode: OpCode.Move, Operands: [_, var source] })
                value = source;
            return value;
        }
        var changed = false;
        foreach (var phi in phis)
        {
            var destination = (LocalVariable)phi.Destination!;
            TypeAnalysisContext? type = null;
            var seeds = new List<IOperand>();
            var updates = new List<LocalVariable>();
            var valid = true;
            foreach (var input in phi.Operands.Skip(1))
            {
                var value = Value(input);
                if (value is Immediate)
                {
                    seeds.Add(value);
                    continue;
                }
                if (value is not LocalVariable update || !definitions.TryGetValue(update, out var definition)
                    || definition is not { OpCode: OpCode.Add or OpCode.Subtract, Operands: [_, var left, var right] })
                { valid = false; break; }
                left = Value(left);
                right = Value(right);
                var stepType = ReferenceEquals(left, destination) ? KnownIntegerType(right, method)
                    : ReferenceEquals(right, destination) ? KnownIntegerType(left, method) : null;
                if (stepType == null || type != null && type != stepType || update.Type != null && update.Type != stepType)
                { valid = false; break; }
                type = stepType;
                updates.Add(update);
            }
            if (!valid || type == null || seeds.Count == 0 || !seeds.All(seed => LiteralFits(seed, type)))
                continue;
            changed |= SetTypeIfUnknown(destination, type);
            foreach (var update in updates)
                changed |= SetTypeIfUnknown(update, type);
        }
        return changed;
    }

    // A local assigned a float/double literal (a lifted rodata constant load) is that float type
    private static void SeedFloatLiterals(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Move || instruction.Operands[0] is not LocalVariable destination)
                continue;

            destination.Type = instruction.Operands[1] switch
            {
                FloatLiteral => method.AppContext.SystemTypes.SystemSingleType,
                DoubleLiteral => method.AppContext.SystemTypes.SystemDoubleType,
                _ => destination.Type,
            };
        }
    }

    // Arithmetic on a float operand is float arithmetic, so the result is that float type.
    private static bool PropagateArithmetic(Instruction instruction, MethodAnalysisContext method)
    {
        if (instruction.Operands is not [LocalVariable { Type: null } destination, var left, var right])
            return false;

        if ((FloatOperandType(left, method) ?? FloatOperandType(right, method)) is not { } floatType)
            return false;

        return SetTypeIfUnknown(destination, floatType);
    }

    // Do not infer integer arithmetic from just one operand: the other may be an
    // unresolved pointer. Require both operands to have the same promoted integer
    // type, or a known integer and a representable literal.
    private static bool PropagateKnownIntegerArithmetic(Instruction instruction, MethodAnalysisContext method)
    {
        if (instruction.Operands is not [LocalVariable { Type: null } destination, var left, var right])
            return false;

        var leftType = KnownIntegerType(left, method);
        var rightType = KnownIntegerType(right, method);
        if (leftType != null && rightType != null && leftType == rightType)
            return SetTypeIfUnknown(destination, leftType);
        if (leftType != null && LiteralFits(right, leftType))
            return SetTypeIfUnknown(destination, leftType);
        if (rightType != null && LiteralFits(left, rightType))
            return SetTypeIfUnknown(destination, rightType);
        return false;
    }

    private static TypeAnalysisContext? KnownIntegerType(IOperand operand, MethodAnalysisContext method)
    {
        var type = operand switch
        {
            LocalVariable local => local.Type,
            FieldReference field => field.Field.FieldType,
            _ => null,
        };
        // Native enum arithmetic operates on its declared underlying integer, not an object.
        if (type?.IsEnumType == true)
            type = type.EnumUnderlyingType;
        return type?.FullName switch
        {
            "System.Byte" or "System.SByte" or "System.Int16" or "System.UInt16" or "System.Char"
                => method.AppContext.SystemTypes.SystemInt32Type,
            "System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64" => type,
            _ => null,
        };
    }

    private static bool LiteralFits(IOperand operand, TypeAnalysisContext type) => operand is Immediate immediate
        && type.FullName switch
        {
            "System.Int32" => immediate.Value is >= int.MinValue and <= int.MaxValue,
            "System.UInt32" => immediate.Value is >= 0 and <= uint.MaxValue,
            "System.Int64" => true,
            "System.UInt64" => immediate.Value >= 0,
            _ => false,
        };

    // An integer operand makes the result an integer. Excludes bool operands so flag logic stays boolean.
    private static bool PropagateIntegerResult(Instruction instruction, MethodAnalysisContext method)
    {
        if (instruction.Operands[0] is not LocalVariable { Type: null } destination)
            return false;

        // A shift count says nothing about the shifted value's width or signedness.
        // In particular, an Int32 count must not turn an unknown 64-bit value into Int32.
        if (instruction.OpCode is OpCode.ShiftLeft or OpCode.ShiftRight)
            return SetTypeIfUnknown(destination, KnownIntegerType(instruction.Operands[1], method));

        for (var i = 1; i < instruction.Operands.Count; i++)
            if (IntegerResultType(instruction.Operands[i], method) is { } integerType)
                return SetTypeIfUnknown(destination, integerType);

        return false;
    }

    // Flag expressions are represented with the same bitwise opcodes as integer arithmetic. Preserve
    // their boolean type so branch conditions do not degrade to object locals in generated IL.
    private static bool PropagateBooleanResult(Instruction instruction, MethodAnalysisContext method)
    {
        if (instruction.Operands[0] is not LocalVariable { Type: null } destination)
            return false;

        if (instruction.OpCode == OpCode.Not)
            return IsBoolean(instruction.Operands[1], method)
                && SetTypeIfUnknown(destination, method.AppContext.SystemTypes.SystemBooleanType);

        if (instruction.OpCode is (OpCode.And or OpCode.Or or OpCode.Xor)
            && IsBoolean(instruction.Operands[1], method)
            && IsBoolean(instruction.Operands[2], method))
            return SetTypeIfUnknown(destination, method.AppContext.SystemTypes.SystemBooleanType);

        return false;
    }

    private static bool IsBoolean(IOperand operand, MethodAnalysisContext method)
        => operand is LocalVariable { Type: { } type }
           && type == method.AppContext.SystemTypes.SystemBooleanType;

    private static TypeAnalysisContext? IntegerResultType(IOperand operand, MethodAnalysisContext method)
    {
        var type = operand switch
        {
            LocalVariable { Type: { } localType } => localType,
            FieldReference field => field.Field.FieldType,
            _ => null,
        };

        return type?.FullName switch
        {
            "System.Byte" or "System.SByte" or "System.Int16" or "System.UInt16"
                or "System.Int32" or "System.UInt32" or "System.Char" => method.AppContext.SystemTypes.SystemInt32Type,
            "System.Int64" or "System.UInt64" => method.AppContext.SystemTypes.SystemInt64Type,
            _ => null,
        };
    }

    private static TypeAnalysisContext? FloatOperandType(IOperand operand, MethodAnalysisContext method) =>
        operand switch
        {
            FloatLiteral => method.AppContext.SystemTypes.SystemSingleType,
            DoubleLiteral => method.AppContext.SystemTypes.SystemDoubleType,
            LocalVariable { Type: { FullName: "System.Single" } single } => single,
            LocalVariable { Type: { FullName: "System.Double" } @double } => @double,
            _ => null,
        };

    private static bool PropagateMove(Instruction move, int pointerSize)
    {
        var destination = move.Operands[0];
        var source = move.Operands[1];

        // Move local, local: copy a known type in whichever direction is missing it.
        if (destination is LocalVariable destLocal && source is LocalVariable sourceLocal)
            return SetTypeIfUnknown(destLocal, sourceLocal.Type) || SetTypeIfUnknown(sourceLocal, destLocal.Type);

        // Move local, field: a field load types its result with the field's type. This is the edge
        // that lets the loaded value go on to be the base of a further field access.
        if (destination is LocalVariable loadDest && source is FieldReference loadField)
            return SetTypeIfUnknown(loadDest, loadField.Field.FieldType);

        // Move field, local: a field store types the stored value with the field's type.
        if (destination is FieldReference storeField && source is LocalVariable storeSource)
            return SetTypeIfUnknown(storeSource, storeField.Field.FieldType);

        // An element of T[] is a T, whether we loaded it (reference arrays) or only computed its address
        if (destination is LocalVariable { Type: null } elementDest
            && source is MemoryOperand { Base: LocalVariable { Type: SzArrayTypeAnalysisContext { ElementType: { } elementType } } } elementAccess
            && (elementAccess.Index != null || elementAccess.Addend >= 4L * pointerSize))
            return SetTypeIfUnknown(elementDest, elementType);

        // Move local, [byref]: dereferencing a managed pointer to a reference type yields that referent
        // (a struct byref accesses fields directly with no deref, so this only fires for class referents).
        if (destination is LocalVariable { Type: null } derefDest
            && source is MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable { Type: ByRefTypeAnalysisContext { ElementType: { IsValueType: false } referent } } })
            return SetTypeIfUnknown(derefDest, referent);

        // Move local, [obj]: offset 0 of a reference-typed value is its klass pointer.
        if (destination is LocalVariable { Type: null } klassDest
            && source is MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable { Type: { } baseType } }
            && baseType is not (RuntimeClassTypeAnalysisContext or StaticFieldStorageTypeAnalysisContext or RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext or ByRefTypeAnalysisContext)
            && !baseType.IsValueType)
            return SetTypeIfUnknown(klassDest, new RuntimeClassTypeAnalysisContext(baseType, baseType.DeclaringAssembly));

        return false;
    }

    // A phi is a copy from each predecessor's value, so types flow both ways across it - mirroring
    // the bidirectional Move copies it decays into once SSA is destroyed.
    private static bool PropagatePhi(Instruction phi)
    {
        if (phi.Operands[0] is not LocalVariable destination)
            return false;

        var changed = false;

        // Forward: an untyped phi result takes the type of any typed input.
        if (destination.Type == null)
        {
            for (var i = 1; i < phi.Operands.Count; i++)
            {
                if (phi.Operands[i] is LocalVariable { Type: { } inputType })
                {
                    changed = SetTypeIfUnknown(destination, inputType);
                    break;
                }
            }
        }

        // Backward: a typed phi result types each of its still-untyped inputs.
        if (destination.Type != null)
        {
            for (var i = 1; i < phi.Operands.Count; i++)
            {
                if (phi.Operands[i] is LocalVariable input)
                    changed |= SetTypeIfUnknown(input, destination.Type);
            }
        }

        return changed;
    }

    private static bool PropagateFromCallParameters(MethodAnalysisContext method)
    {
        var changed = false;

        // A lea and the call it's passed to are still separate here. The address only gets folded into the
        // call later, so an argument's address-of has to be found through the local carrying it.
        var addressesOf = new Dictionary<LocalVariable, LocalVariable>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode == OpCode.Move
                && instruction.Operands[0] is LocalVariable pointer
                && instruction.Operands[1] is AddressOf { Target: LocalVariable pointee })
                addressesOf[pointer] = pointee;
        }

        // A copy of a typed local gets its type from that local; the callee's declaring type may be a base
        // class of it (e.g. Component for a copy of 'this' passed to get_gameObject).
        var copySources = new Dictionary<LocalVariable, LocalVariable?>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
            if (instruction.Destination is LocalVariable destination)
                copySources[destination] = !copySources.ContainsKey(destination)
                    && instruction is { OpCode: OpCode.Move, Operands: [_, LocalVariable source] } ? source : null;
        bool CopiesTypedLocal(LocalVariable local)
        {
            for (var hops = 0; hops < 8 && copySources.TryGetValue(local, out var source) && source != null; hops++, local = source)
                if (source.Type != null)
                    return true;
            return false;
        }

        LocalVariable? Addressed(IOperand operand) => operand switch
        {
            AddressOf { Target: LocalVariable direct } => direct,
            LocalVariable local when addressesOf.TryGetValue(local, out var indirect) => indirect,
            _ => null
        };

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (!instruction.IsCall)
                continue;

            if (instruction.Operands[0] is not MethodAnalysisContext calledMethod)
                continue;

            // Return value: a constructor yields its declaring type, otherwise the declared return type.
            if (instruction.Destination is LocalVariable returnValue)
            {
                var producedType = calledMethod.Name is ".ctor" or ".cctor" ? calledMethod.DeclaringType : calledMethod.ReturnType;

                if (producedType != method.AppContext.SystemTypes.SystemVoidType)
                    changed |= SetTypeIfUnknown(returnValue, producedType);
            }


            // Call operands
            // 0. Target
            // 1. ReturnValue
            // 2. thisParam
            // ... parameters

            // CallVoid operands
            // 0. Target
            // 1. thisParam
            // ... parameters
            var thisParamIndex = instruction.OpCode == OpCode.CallVoid ? 1 : 2;

            // 'this' param
            if (!calledMethod.IsStatic
                && instruction.Operands[thisParamIndex] is LocalVariable thisParam && !CopiesTypedLocal(thisParam))
            {
                changed |= SetTypeIfUnknown(thisParam, calledMethod.DeclaringType);
            }

            // Value type instance method, first arg is address of value, but we need to type the value
            if (!calledMethod.IsStatic
                && Addressed(instruction.Operands[thisParamIndex]) is { } addressedReceiver
                && calledMethod.DeclaringType is { IsValueType: true } valueType)
            {
                changed |= SetTypeIfUnknown(addressedReceiver, valueType);
            }

            // Remaining arguments map positionally onto the callee's declared parameters.
            var paramOffset = calledMethod.IsStatic ? 1 : 2;
            if (instruction.OpCode == OpCode.Call) // Skip the return value operand
                paramOffset += 1;

            for (var i = paramOffset; i < instruction.Operands.Count; i++)
            {
                var parameterIndex = i - paramOffset;
                if (parameterIndex > calledMethod.Parameters.Count - 1) // Probably MethodInfo*
                    continue;

                var parameterType = calledMethod.Parameters[parameterIndex].ParameterType;

                if (parameterType is ByRefTypeAnalysisContext { ElementType: { } referencedType }
                    && Addressed(instruction.Operands[i]) is { } referenced)
                {
                    changed |= SetTypeIfUnknown(referenced, referencedType);
                    continue;
                }

                if (instruction.Operands[i] is LocalVariable local)
                    changed |= SetTypeIfUnknown(local, parameterType);
            }
        }

        return changed;
    }

    private static void PropagateFromParameters(MethodAnalysisContext method)
    {
        // 'this'
        if (!method.IsStatic)
        {
            var thisLocal = method.ParameterLocals.FirstOrDefault(p => p.IsThis);
            if (thisLocal != null)
                thisLocal.Type = method.DeclaringType is { GenericParameters.Count: > 0 } generic
                    ? new GenericInstanceTypeAnalysisContext(generic, generic.GenericParameters)
                    : method.DeclaringType;
        }

        if (method.ParameterLocals.FirstOrDefault(p => p.IsMethodInfo) is { } methodInfoLocal && method.DeclaringType is { } owner)
            methodInfoLocal.Type = new RuntimeMethodInfoAnalysisContext(method, owner.DeclaringAssembly);

        if (method.Parameters.Count == 0)
            return;

        // Normal params
        var paramIndex = 0;
        foreach (var local in method.ParameterLocals)
        {
            if (local.IsThis || local.IsMethodInfo)
                continue;

            if (paramIndex >= method.Parameters.Count)
                break;

            local.Type = method.Parameters[paramIndex].ParameterType;
            paramIndex++;
        }
    }

    private static void PropagateFromReturn(MethodAnalysisContext method)
    {
        var returns = method.ControlFlowGraph!.Instructions.Where(i => i.OpCode == OpCode.Return);

        foreach (var instruction in returns)
        {
            if (instruction.Operands.Count == 1 && instruction.Operands[0] is LocalVariable local)
                local.Type = method.ReturnType;
        }
    }
}
