using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

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
            locals.Add(register, new LocalVariable($"v{i}", register));
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
            // Typing the unversioned parameter slot lets struct-typed parameters (UniTask,
            // awaiters, vectors) resolve field accesses through their stack copies.
            SetTypeIfUnknown(local, method.Parameters[i].ParameterType);
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
        SeedComparisonResults(method);
        SeedFloatLiterals(method);

        // Everywhere there's a CallVoid after a Newobj, we can resolve the constructor call.
        MetadataResolver.ResolveConstructorCalls(method);

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
            changed |= MetadataResolver.ResolveCallsViaMethodInfo(method);
            changed |= MetadataResolver.ResolveAmbiguousCalls(method);
            changed |= MetadataResolver.ResolveVirtualCalls(method);
            changed |= PropagateFromCallParameters(method);
            changed |= MetadataResolver.ResolveFieldOffsets(method);
            changed |= RgctxResolver.Run(method);
            changed |= PropagateStaticFieldStorage(method);
            changed |= TypeAddressedLocals(method);
            changed |= PropagateStackSlotTypes(method);
            changed |= PropagateTypesOnce(method);
        }
    }

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

        foreach (var block in method.ControlFlowGraph!.Blocks)
        {
            foreach (var instruction in block.Instructions)
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

                    // For concrete generic callees, substitute the actual type arguments so e.g.
                    // ref TAwaiter lands as ref UniTask<T>.Awaiter instead of the bare parameter.
                    var parameterType = calledMethod.Parameters[parameterIndex].ParameterType;

                    if (calledMethod is ConcreteGenericMethodAnalysisContext concrete)
                        parameterType = GenericInstantiation.Instantiate(parameterType, concrete.TypeGenericParameters, concrete.MethodGenericParameters);

                    if (instruction.Operands[i] is AddressOf { Target: LocalVariable referenced }
                        && parameterType is ByRefTypeAnalysisContext { ElementType: { } referencedType })
                        changed |= SetTypeIfUnknown(referenced, referencedType);
                }

                // A callee returning a large struct takes a hidden return buffer in rcx, which is
                // not in the operand list; the buffer's type is the callee's return type.
                if (calledMethod.AppContext.InstructionSet.CallingConventionResolver?.ReturnsViaHiddenBuffer(calledMethod) == true)
                    changed |= TypeHiddenReturnBuffer(method, block, instruction, calledMethod);
            }
        }

        return changed;
    }

    private static bool TypeHiddenReturnBuffer(MethodAnalysisContext method, Graphs.Block block, Instruction call, MethodAnalysisContext calledMethod)
    {
        for (var j = block.Instructions.IndexOf(call) - 1; j >= 0; j--)
        {
            var candidate = block.Instructions[j];

            if (candidate.OpCode is OpCode.Call or OpCode.CallVoid or OpCode.IndirectCall)
                return false; // rcx belongs to an earlier call, don't guess across it

            // SSA versioning renames registers (rcx -> rcx_v5)
            static bool IsRcx(IOperand operand) =>
                operand is LocalVariable { Register.Name: { } registerName }
                && (registerName is "rcx" or "ecx"
                    || registerName.StartsWith("rcx_v") || registerName.StartsWith("ecx_v"));

            if (candidate.OpCode is OpCode.Add or OpCode.Subtract
                && candidate.Operands is [LocalVariable dest, { } rspSource, ISIL.Immediate offset]
                && IsRcx(dest)
                && rspSource is LocalVariable { Register.Name: "rsp" })
            {
                // lea rcx, [rsp +/- N] - the buffer is the stack slot at that offset, which the
                // stack analyzer names stack_NN
                var slotOffset = candidate.OpCode == OpCode.Add ? offset.Value : -offset.Value;
                var slotName = $"stack_{Math.Abs(slotOffset):X}";
                var slot = method.Locals.FirstOrDefault(l => l.Register.Name == slotName);

                return slot != null && SetTypeIfUnknown(slot, calledMethod.ReturnType);
            }

            if (candidate.OpCode != OpCode.Move || candidate.Operands.Count < 2)
                continue;

            if (!IsRcx(candidate.Operands[0]))
                continue;

            return candidate.Operands[1] is AddressOf { Target: LocalVariable buffer }
                   && SetTypeIfUnknown(buffer, calledMethod.ReturnType);
        }

        return false;
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

    // Locals and parameters stored to a frame slot carry their declared type; a load from the
    // same slot inherits it. This is the main way async state-machine locals (awaiters, tuples,
    // big structs spilled to the frame) get their types.
    public static bool PropagateStackSlotTypes(MethodAnalysisContext method)
    {
        var changed = false;
        var slotTypes = new Dictionary<(string Kind, long Offset), TypeAnalysisContext>();

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Move || instruction.Operands.Count < 2)
                continue;

            if (instruction.Operands[0] is not MemoryOperand { Base: LocalVariable storeBase, Index: null, Scale: 0 } storeMemory)
                continue;

            if (!TryGetStackSlotKey(storeBase, storeMemory.Addend, out var key))
                continue;

            var sourceType = instruction.Operands[1] switch
            {
                LocalVariable { Type: { } localType } => localType,
                FieldReference field => field.LeafType,
                _ => null,
            };

            if (sourceType != null && !slotTypes.ContainsKey(key))
                slotTypes.Add(key, sourceType);
        }

        if (slotTypes.Count == 0)
            return false;

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (instruction.OpCode != OpCode.Move || instruction.Operands.Count < 2)
                continue;

            if (instruction.Operands[0] is not LocalVariable { Type: null } loadDest)
                continue;

            if (instruction.Operands[1] is not MemoryOperand { Base: LocalVariable loadBase, Index: null, Scale: 0 } loadMemory)
                continue;

            if (TryGetStackSlotKey(loadBase, loadMemory.Addend, out var loadKey)
                && slotTypes.TryGetValue(loadKey, out var slotType))
                changed |= SetTypeIfUnknown(loadDest, slotType);
        }

        return changed;
    }

    private static bool TryGetStackSlotKey(LocalVariable baseLocal, long addend, out (string Kind, long Offset) key)
    {
        var name = baseLocal.Register.Name;

        if (name is "rsp" or "rbp")
        {
            key = (name, addend);
            return true;
        }

        if (name is { Length: > 6 } && name.StartsWith("stack_")
            && long.TryParse(name[6..], System.Globalization.NumberStyles.AllowHexSpecifier | System.Globalization.NumberStyles.AllowLeadingSign,
                System.Globalization.CultureInfo.InvariantCulture, out var slotOffset))
        {
            key = ("stack", slotOffset + addend);
            return true;
        }

        key = default;
        return false;
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
                    changed |= PropagateMove(instruction, method);
                    break;
                case OpCode.Unbox:
                    if (instruction.Operands is [LocalVariable { Type: null } unboxedDest, _, TypeAnalysisContext unboxedType])
                        changed |= SetTypeIfUnknown(unboxedDest, unboxedType);
                    break;
                case OpCode.Box:
                    if (instruction.Operands is [LocalVariable { Type: null } boxDest, TypeAnalysisContext boxType, _])
                        changed |= SetTypeIfUnknown(boxDest, boxType);
                    break;
                case OpCode.IsInst:
                    // isinst(x, T) yields an instance of T or null: the result type is T, which
                    // may be narrower than the propagated source type (object / a base class).
                    // Narrowing here is what lets subsequent field access on the cast result work.
                    if (instruction.Operands is [LocalVariable isinstDest, _, TypeAnalysisContext isinstType]
                        && !isinstType.IsValueType
                        && !ReferenceEquals(isinstDest.Type, isinstType)
                        && IsBroaderThan(isinstDest.Type, isinstType))
                    {
                        isinstDest.Type = isinstType;
                        changed = true;
                    }
                    break;
                case >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual:
                    if (instruction.Operands[0] is LocalVariable { Type: null } checkDest)
                        changed |= SetTypeIfUnknown(checkDest, method.AppContext.SystemTypes.SystemBooleanType);
                    break;
                case OpCode.Phi:
                    changed |= PropagatePhi(instruction);
                    break;
                case OpCode.Add or OpCode.Subtract or OpCode.Multiply:
                    changed |= PropagateArithmetic(instruction, method);
                    break;
                case OpCode.Divide or OpCode.Modulo:
                    changed |= PropagateArithmetic(instruction, method) || PropagateIntegerResult(instruction, method);
                    break;
                case OpCode.And or OpCode.Or or OpCode.Xor or OpCode.Not or OpCode.Negate
                    or OpCode.ShiftLeft or OpCode.ShiftRight:
                    changed |= PropagateIntegerResult(instruction, method);
                    break;
            }
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

    // An integer operand makes the result an integer. Excludes bool operands so flag logic stays boolean.
    private static bool PropagateIntegerResult(Instruction instruction, MethodAnalysisContext method)
    {
        if (instruction.Operands[0] is not LocalVariable { Type: null } destination)
            return false;

        for (var i = 1; i < instruction.Operands.Count; i++)
            if (IntegerResultType(instruction.Operands[i], method) is { } integerType)
                return SetTypeIfUnknown(destination, integerType);

        return false;
    }

    private static TypeAnalysisContext? IntegerResultType(IOperand operand, MethodAnalysisContext method)
    {
        var type = operand switch
        {
            LocalVariable { Type: { } localType } => localType,
            FieldReference field => field.LeafType,
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

    // Whether 'current' is a supertype of 'narrow' (or unknown), so an isinst result may be
    // narrowed to it. Interfaces are always considered broader - the isinst result implements
    // them by construction, and the concrete type is the more useful label.
    private static bool IsBroaderThan(TypeAnalysisContext? current, TypeAnalysisContext narrow)
    {
        if (current == null)
            return true;

        if (current.IsInterface)
            return true;

        for (var t = narrow.BaseType; t != null; t = t.BaseType)
            if (ReferenceEquals(t, current))
                return true;

        return false;
    }

    private static bool PropagateMove(Instruction move, MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var destination = move.Operands[0];
        var source = move.Operands[1];

        // Move local, local: copy a known type in whichever direction is missing it.
        if (destination is LocalVariable destLocal && source is LocalVariable sourceLocal)
            return SetTypeIfUnknown(destLocal, sourceLocal.Type) || SetTypeIfUnknown(sourceLocal, destLocal.Type);

        // Move local, array.Length: the length is always an int
        if (destination is LocalVariable { Type: null } lengthDest && source is ArrayLength)
            return SetTypeIfUnknown(lengthDest, method.AppContext.SystemTypes.SystemInt32Type);

        // Move local, &local: a byref-typed pointer tells us the pointee's type. The reverse is
        // done only for value-type pointees: &local of a struct is the ((T*)&local)->field
        // pattern IL2CPP emits for ref struct locals, while a reference-type address-of is a
        // reference slot or raw buffer where byref typing misdirects field resolution.
        if (destination is LocalVariable ptrDest && source is AddressOf { Target: LocalVariable pointee })
        {
            if (ptrDest.Type is ByRefTypeAnalysisContext { ElementType: { } pointeeElement })
                return SetTypeIfUnknown(pointee, pointeeElement);

            if (pointee.Type is { IsValueType: true } pointeeType)
                return SetTypeIfUnknown(ptrDest, new ByRefTypeAnalysisContext(pointeeType));

            return false;
        }

        // Move local, field: a field load types its result with the field's type. This is the edge
        // that lets the loaded value go on to be the base of a further field access.
        if (destination is LocalVariable loadDest && source is FieldReference loadField)
            return SetTypeIfUnknown(loadDest, loadField.LeafType);

        // Move field, local: a field store types the stored value with the field's type.
        if (destination is FieldReference storeField && source is LocalVariable storeSource)
            return SetTypeIfUnknown(storeSource, storeField.LeafType);

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

                // Substitute actual type arguments for concrete generic callees (TResult -> the
                // instantiated type), so the result isn't typed as a bare generic parameter.
                if (calledMethod is ConcreteGenericMethodAnalysisContext concreteCallee)
                    producedType = GenericInstantiation.Instantiate(producedType, concreteCallee.TypeGenericParameters, concreteCallee.MethodGenericParameters);

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
                && instruction.Operands[thisParamIndex] is LocalVariable thisParam)
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

                    // The pointer local itself is confirmed to be a managed byref here (not a
                    // raw buffer), so [ptr + X] can resolve through the pointee layout.
                    if (instruction.Operands[i] is LocalVariable pointerLocal)
                        changed |= SetTypeIfUnknown(pointerLocal, parameterType);

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
