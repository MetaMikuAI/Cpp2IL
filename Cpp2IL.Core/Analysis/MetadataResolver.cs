using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL;

namespace Cpp2IL.Core.Analysis;

public static class MetadataResolver
{
    public static void ResolveAll(MethodAnalysisContext method)
    {
        ResolveStringLiteralAccessors(method);
        ResolveCalls(method);
        ResolveGetter(method);
        ResolveMetadataUsages(method);
    }

    private static void ResolveStringLiteralAccessors(MethodAnalysisContext method)
    {
        var libContext = method.AppContext.LibCpp2IlContext;

        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
            if (instruction.Destination is LocalVariable destination)
                definitions[destination] = instruction;

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (instruction.OpCode != OpCode.Call || instruction.Operands[1] is not LocalVariable result)
                continue;

            for (var i = 2; i < instruction.Operands.Count; i++)
            {
                if (LiteralSlotAddress(instruction.Operands[i], definitions) is not { } address
                    || libContext.GetLiteralByAddress(address) is not { } literal)
                    continue;

                instruction.OpCode = OpCode.Move;
                instruction.SetOperands(result, new StringLiteral(literal));
                break;
            }
        }
    }

    private static ulong? LiteralSlotAddress(IOperand operand, Dictionary<LocalVariable, Instruction> definitions) =>
        operand switch
        {
            Immediate immediate => immediate.UnsignedValue,
            LocalVariable local when definitions.TryGetValue(local, out var definition)
                && definition is { OpCode: OpCode.Move, Operands: [_, Immediate immediate] } => immediate.UnsignedValue,
            _ => null,
        };

    /// <summary>
    /// Resolves <c>Move local, [absoluteAddress]</c> loads of IL2CPP metadata-usage globals into a
    /// strongly-typed operand: a string literal, a <see cref="TypeAnalysisContext"/> (an Il2CppType*/
    /// Il2CppClass* usage) or, for a MethodInfo* usage, a <see cref="RuntimeMethodInfoAnalysisContext"/>
    /// naming the method it refers to (also used to type the local - see <see cref="LocalVariables"/>),
    /// or likewise a <see cref="RuntimeFieldInfoAnalysisContext"/> for a FieldInfo* usage.
    /// </summary>
    private static void ResolveMetadataUsages(MethodAnalysisContext method)
    {
        var libContext = method.AppContext.LibCpp2IlContext;
        var resolvedMetadataPointers = new Dictionary<LocalVariable, IOperand>();

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Move)
                continue;

            if (instruction.Operands[0] is not LocalVariable destination)
                continue;

            // v27+ 元数据全局通常通过两次加载表示：第一次取得元数据槽地址，第二次解引用该地址。
            // 将已解析的用法沿间接层传递，使 MethodInfo/FieldInfo 操作数参与正常类型传播。
            if (instruction.Operands[1] is MemoryOperand
                {
                    Base: LocalVariable pointer,
                    Index: null,
                    Addend: 0,
                    Scale: 0
                }
                && resolvedMetadataPointers.TryGetValue(pointer, out var resolvedPointer))
            {
                instruction.SetOperand(1, resolvedPointer);
                resolvedMetadataPointers[destination] = resolvedPointer;
                continue;
            }

            var address = instruction.Operands[1] switch
            {
                MemoryOperand { Base: null, Index: null, Scale: 0 } memory => (ulong)memory.Addend,
                Immediate immediate => immediate.UnsignedValue,
                _ => 0ul,
            };

            if (address == 0)
                continue;

            // String literal.
            var stringLiteral = libContext.GetLiteralByAddress(address);
            if (stringLiteral != null)
            {
                var resolved = new StringLiteral(stringLiteral);
                instruction.SetOperand(1, resolved);
                resolvedMetadataPointers[destination] = resolved;
                continue;
            }

            // Type metadata usage (Il2CppType* / Il2CppClass*).
            if (method.DeclaringType is { } declaringType)
            {
                var typeGlobal = libContext.GetTypeGlobalByAddress(address);
                if (typeGlobal != null)
                {
                    var resolved = declaringType.AppContext.ResolveIl2CppType(typeGlobal);
                    instruction.SetOperand(1, resolved);
                    resolvedMetadataPointers[destination] = resolved;
                    continue;
                }
            }

            // Method metadata usage (MethodInfo*). On metadata v27+ GetMethodGlobalByAddress can return
            // any global, so confirm it is actually a method before resolving - the resolver's switch
            // throws on other usage kinds.
            var methodUsage = libContext.GetMethodGlobalByAddress(address);
            if (methodUsage?.Type is MetadataUsageType.MethodDef or MetadataUsageType.MethodRef
                && method.AppContext.ResolveContextForMethod(methodUsage) is { DeclaringType: { } methodDeclaringType } methodContext)
            {
                var resolved = new RuntimeMethodInfoAnalysisContext(methodContext, methodDeclaringType.DeclaringAssembly);
                instruction.SetOperand(1, resolved);
                resolvedMetadataPointers[destination] = resolved;
                continue;
            }

            // Field metadata usage (FieldInfo*), e.g. the RuntimeFieldHandle passed to InitializeArray.
            if (libContext.GetRawFieldGlobalByAddress(address) is { Type: MetadataUsageType.FieldInfo } fieldUsage
                && method.AppContext.ResolveContextForField(fieldUsage.AsField()) is { DeclaringType.DeclaringAssembly: { } fieldAssembly } fieldContext)
            {
                var resolved = new RuntimeFieldInfoAnalysisContext(fieldContext, fieldAssembly);
                instruction.SetOperand(1, resolved);
                resolvedMetadataPointers[destination] = resolved;
            }
        }
    }

    /// <summary>
    /// Replaces every <c>[base + addend]</c> memory operand whose base is a typed local with a
    /// <see cref="FieldReference"/> to the field at that offset. Returns whether any operand was
    /// resolved this pass, so the type/field fixpoint can detect convergence: as more bases become
    /// typed (a field load types its result, which is the base of the next load), more offsets
    /// resolve, so this is re-run until it stops finding new fields.
    /// </summary>
    public static bool ResolveFieldOffsets(MethodAnalysisContext method)
    {
        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
            if (instruction.Destination is LocalVariable destination)
                definitions[destination] = instruction;

        var changed = false;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                var operand = instruction.Operands[i];

                // StackAnalyzer names each frame slot independently. A large value type returned
                // through ARM64 X8 spans several such slots, so a later load of (base + field
                // offset) arrives as a plain local instead of a MemoryOperand. Reconnect that slot
                // to its enclosing value type before normal propagation handles the loaded type.
                if (instruction.OpCode == OpCode.Move
                    && i == 1
                    && operand is LocalVariable stackFieldLocal
                    && ResolveStackFieldLoad(method, stackFieldLocal) is { } stackField)
                {
                    instruction.SetOperand(i, stackField);
                    operand = stackField;
                    changed = true;
                }

                if (operand is not MemoryOperand memory)
                    continue;

                // Has to be [base (local) + addend (field offset)]
                if (memory.Index != null || memory.Scale != 0)
                    continue;

                if (memory.Base is not LocalVariable local)
                    continue;

                // ARM64 pre/post-indexed stores are represented as an Add updating the base
                // register followed by a zero-offset memory access. Follow that address update
                // so the effective offset can still be matched to a managed field.
                var fieldLocal = local;
                var fieldOffset = memory.Addend;
                UnwrapAddressUpdate(ref fieldLocal, ref fieldOffset, definitions);

                if (fieldLocal.Type == null)
                    continue;

                // check if static field access
                var staticOwner = (fieldLocal.Type as StaticFieldStorageTypeAnalysisContext)?.OwnerType;
                var owner = staticOwner ?? fieldLocal.Type;
                var genericOwner = owner as GenericInstanceTypeAnalysisContext;
                GenericInstanceTypeAnalysisContext? fieldGenericOwner = genericOwner;

                // Search the complete inheritance chain. Generic base classes have zero metadata
                // offsets, so compute their instantiated layout and retain the concrete owner for
                // field type substitution (e.g. ResourcePool<AreaObjectCharacter>.resources).
                FieldAnalysisContext? field = null;
                for (var candidateOwner = owner; candidateOwner != null && field == null; candidateOwner = candidateOwner.BaseType)
                {
                    if (staticOwner == null && candidateOwner is GenericInstanceTypeAnalysisContext candidateGeneric)
                    {
                        if (candidateGeneric.GenericArguments.Any(a => a.IsValueType))
                            continue;

                        field = GenericInstanceFieldLayout.FindFieldAtOffset(candidateGeneric.GenericType, fieldOffset);
                        if (field != null)
                            fieldGenericOwner = candidateGeneric;

                        continue;
                    }

                    if (staticOwner == null && candidateOwner.GenericParameters.Count > 0)
                    {
                        field = GenericInstanceFieldLayout.FindFieldAtOffset(candidateOwner, fieldOffset);
                        continue;
                    }

                    field = candidateOwner.Fields.FirstOrDefault(f => f.IsStatic == (staticOwner != null)
                        && (f.Attributes & FieldAttributes.Literal) == 0 // consts have no storage but their metadata offset is 0, which would match
                        && f.BackingData?.FieldOffset == fieldOffset);
                }

                if (field == null)
                {
                    // A pair load/store can address a member inside an embedded value type, e.g.
                    // Vector2.y at outerFieldOffset + 4. Resolve the innermost field so IL generation
                    // can use ldflda/stfld instead of leaving an untyped raw memory write behind.
                    for (var candidateOwner = genericOwner?.GenericType ?? owner;
                         candidateOwner != null && field == null;
                         candidateOwner = candidateOwner.BaseType)
                    {
                        var containing = candidateOwner.Fields.FirstOrDefault(f => !f.IsStatic
                            && f.FieldType.IsValueType
                            && f.Offset >= 0
                            && f.FieldType.Fields.Any(n => !n.IsStatic
                                && n.Offset == fieldOffset - f.Offset));

                        if (containing?.FieldType.Fields.FirstOrDefault(f => !f.IsStatic
                                && f.Offset == fieldOffset - containing.Offset) is { } nested)
                        {
                            field = nested;
                            instruction.SetOperand(i, new FieldReference(field, fieldLocal, (int)fieldOffset, containing));
                        }
                    }

                    if (field == null)
                        continue;
                }

                // A scalar store at the start of an embedded value type is a store to its first
                // member, not an assignment of the whole aggregate (e.g. Vector2.x). The native
                // compiler commonly emits this shape when initializing one component separately.
                if (instruction.OpCode == OpCode.Move
                    && instruction.Operands[0] is MemoryOperand
                    && field.FieldType.IsValueType
                    && OperandType(instruction.Operands[1], method, definitions) is { } storedType
                    && field.FieldType.FullName != storedType.FullName
                    && field.FieldType.Fields.FirstOrDefault(n => !n.IsStatic && n.Offset == 0
                        && n.FieldType.FullName == storedType.FullName) is { } firstMember)
                {
                    instruction.SetOperand(i, new FieldReference(firstMember, fieldLocal, (int)fieldOffset, field));
                }

                // make sure we have a full GIT for field access. open type is bad.
                if (fieldGenericOwner != null && instruction.Operands[i] is not FieldReference { IsNested: true })
                    field = new ConcreteGenericFieldAnalysisContext(field, fieldGenericOwner);

                if (instruction.Operands[i] is not FieldReference { IsNested: true })
                    instruction.SetOperand(i, new FieldReference(field, fieldLocal, (int)fieldOffset));
                changed = true;
            }
        }

        return changed;
    }

    private static FieldReference? ResolveStackFieldLoad(MethodAnalysisContext method, LocalVariable fieldLocal)
    {
        if (!TryGetStackOffset(fieldLocal, out var fieldOffset))
            return null;

        foreach (var baseLocal in method.Locals)
        {
            if (ReferenceEquals(baseLocal, fieldLocal)
                || !TryGetStackOffset(baseLocal, out var baseOffset)
                || baseOffset >= fieldOffset
                || baseLocal.Type is not { IsValueType: true } baseType)
                continue;

            var relativeOffset = fieldOffset - baseOffset;
            var definition = baseType is GenericInstanceTypeAnalysisContext generic
                ? generic.GenericType
                : baseType;
            var field = GenericInstanceFieldLayout.FindFieldAtUnboxedOffset(definition, relativeOffset);
            if (field == null)
                continue;

            if (baseType is GenericInstanceTypeAnalysisContext genericOwner)
                field = new ConcreteGenericFieldAnalysisContext(field, genericOwner);

            return new FieldReference(field, baseLocal, (int)relativeOffset);
        }

        return null;
    }

    private static bool TryGetStackOffset(LocalVariable local, out long offset)
    {
        var name = local.Register.Name;
        if (name is not { Length: > 6 } || !name.StartsWith("stack_", StringComparison.Ordinal))
        {
            offset = 0;
            return false;
        }

        var text = name[6..];
        var negative = text.StartsWith("-", StringComparison.Ordinal);
        if (negative)
            text = text[1..];

        if (!long.TryParse(text, NumberStyles.AllowHexSpecifier, CultureInfo.InvariantCulture, out var magnitude))
        {
            offset = 0;
            return false;
        }

        offset = negative ? -magnitude : magnitude;
        return true;
    }

    private static TypeAnalysisContext? OperandType(IOperand operand, MethodAnalysisContext method,
        Dictionary<LocalVariable, Instruction> definitions) => OperandType(operand, method, definitions, []);

    private static TypeAnalysisContext? OperandType(IOperand operand, MethodAnalysisContext method,
        Dictionary<LocalVariable, Instruction> definitions, HashSet<LocalVariable> visited) => operand switch
    {
        LocalVariable { Type: { } type } => type,
        LocalVariable local when visited.Add(local)
            && definitions.TryGetValue(local, out var definition)
            && definition.Operands.Count > 1
            => OperandType(definition.Operands[1], method, definitions, visited),
        FieldReference field => field.Field.FieldType,
        FloatLiteral => method.AppContext.SystemTypes.SystemSingleType,
        DoubleLiteral => method.AppContext.SystemTypes.SystemDoubleType,
        _ => null
    };

    private static void UnwrapAddressUpdate(ref LocalVariable local, ref long offset,
        Dictionary<LocalVariable, Instruction> definitions)
    {
        var visited = new HashSet<LocalVariable>();

        while (visited.Add(local)
            && definitions.TryGetValue(local, out var definition)
            && definition.OpCode == OpCode.Add
            && definition.Operands.Count >= 3)
        {
            LocalVariable? source = null;
            Immediate addend;

            if (definition.Operands[1] is LocalVariable left && definition.Operands[2] is Immediate right)
            {
                source = left;
                addend = right;
            }
            else if (definition.Operands[1] is Immediate leftImmediate && definition.Operands[2] is LocalVariable rightLocal)
            {
                source = rightLocal;
                addend = leftImmediate;
            }
            else
            {
                break;
            }

            offset = unchecked(offset + addend.Value);
            local = source;
        }
    }

    private static void ResolveCalls(MethodAnalysisContext method)
    {
        foreach (var block in method.ControlFlowGraph!.Blocks)
        {
            if (block.BlockType != BlockType.Call && block.BlockType != BlockType.TailCall)
                continue;

            var callInstruction = block.Instructions[^1];
            if (callInstruction.Operands[0] is not Immediate dest)
                continue;

            var target = dest.UnsignedValue;

            var keyFunctionAddresses = method.AppContext.GetOrCreateKeyFunctionAddresses();

            if (keyFunctionAddresses.IsKeyFunctionAddress(target))
            {
                HandleKeyFunction(method.AppContext, callInstruction, target, keyFunctionAddresses);

                if (target == keyFunctionAddresses.il2cpp_codegen_initialize_runtime_metadata_inline
                    && callInstruction is { OpCode: OpCode.Call, Operands: [_, var initResult, var handle, ..] })
                {
                    callInstruction.OpCode = OpCode.Move;
                    callInstruction.SetOperands(initResult, handle);
                }

                continue;
            }

            //Non-key function call. Try to find a single match
            if (!method.AppContext.MethodsByAddress.TryGetValue(target, out var targetMethods))
            {
                // Not a managed method at all. It may be one of the runtime helpers built around an exception
                // type, which either throw it themselves or build it and hand it back for the caller to raise.
                if (ThrowHelperRecovery.GetThrownException(method.AppContext, target) is { } thrown)
                {
                    if (ThrowHelperRecovery.IsExceptionRaiser(method.AppContext, target))
                    {
                        callInstruction.OpCode = OpCode.Throw;
                        callInstruction.SetOperands(thrown);
                    }
                    else if (callInstruction.Destination is LocalVariable produced && method.ControlFlowGraph!.Instructions.Any(i => i.Sources.Any(s => ReferenceEquals(s, produced))))
                    {
                        callInstruction.OpCode = OpCode.Newobj;
                        callInstruction.SetOperands(produced, thrown);
                    }
                    else
                    {
                        callInstruction.OpCode = OpCode.Throw;
                        callInstruction.SetOperands(thrown);
                    }

                    continue;
                }

                // Otherwise it may be one of the raisers, which throw the exception they are given
                var raisedIndex = callInstruction.OpCode == OpCode.CallVoid ? 1 : 2;

                if (callInstruction.Operands.Count > raisedIndex && ThrowHelperRecovery.IsExceptionRaiser(method.AppContext, target))
                {
                    var raised = callInstruction.Operands[raisedIndex];

                    if (raised is LocalVariable local)
                        local.Type = method.AppContext.SystemTypes.SystemExceptionType;

                    callInstruction.OpCode = OpCode.Throw;
                    callInstruction.SetOperands(raised);
                }

                continue;
            }

            // Duplicated/Shared method bodies are resolved later in ResolveCallsViaMethodInfo/ResolveAmbiguousCalls.
            // A reference-type generic body is commonly represented by its object instantiation
            // (for example List<object>.Enumerator.Dispose). Binding that placeholder here loses
            // the concrete T when the caller's MethodInfo is unavailable on an exception edge.
            if (targetMethods is not [{ } singleTargetMethod] || IsSharedGenericMethod(singleTargetMethod))
                continue;

            callInstruction.SetOperand(0, singleTargetMethod);
            singleTargetMethod.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(callInstruction, singleTargetMethod);
        }

        method.ControlFlowGraph.MergeCallBlocks();
    }

    /// <summary>
    /// Resolves calls whose address maps to more than one method by matching the receiver's known
    /// type against the candidates' declaring types. Runs inside the type/field fixpoint and so
    /// re-fires as receivers become typed - a resolved call types its return value, which can type
    /// the receiver of a further call. Returns whether any call was resolved this pass.
    ///
    /// Conservative by design: it commits only when exactly one non-static candidate's declaring
    /// type matches the receiver's type. Anything still untyped or ambiguous is left for a later
    /// pass, or left unresolved - it never guesses.
    /// </summary>
    public static bool ResolveAmbiguousCalls(MethodAnalysisContext method)
    {
        var changed = false;
        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.Destination is LocalVariable destination)
                definitions[destination] = instruction;
        }

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (!instruction.IsCall)
                continue;

            // A resolved call's target is a method/key-function name; only unresolved ones are still numeric.
            if (instruction.Operands[0] is not Immediate target)
                continue;

            if (!method.AppContext.MethodsByAddress.TryGetValue(target.UnsignedValue, out var candidates))
                continue;

            // A single candidate can still be a shared generic object body. In that case the
            // receiver carries the concrete instantiation even when no MethodInfo* survived.
            if (candidates is [{ } sharedGeneric]
                && GetReceiver(instruction, definitions) is { Type: { } singleReceiverType }
                && TrySpecializeSharedGeneric(sharedGeneric, singleReceiverType) is { } specialized)
            {
                instruction.SetOperand(0, specialized);
                specialized.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, specialized);
                changed = true;
                continue;
            }

            if (candidates.Count < 2)
                continue;

            // e.g. string.Equals and string.op_Equality, identical params, instance type, and bodies are shared
            // we can't differentiate which is being called but it doesn't matter
            if (AreInterchangeable(candidates))
            {
                var preferred = PreferredOf(candidates);
                instruction.SetOperand(0, preferred);
                preferred.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, preferred);
                changed = true;
                continue;
            }

            if (GetReceiver(instruction, definitions) is not { Type: { } receiverType } receiver)
                continue;

            // Prefer picking base ctor if we are a ctor
            // SSA copies of the implicit `this` parameter do not retain IsThis. Their type still
            // matches the constructor's declaring type, which is enough to identify a base-ctor call.
            var callerIsCtor = method.Name == ".ctor"
                && (receiver.IsThis || IsSameType(receiverType, method.DeclaringType));

            // Generic base constructors are commonly emitted as one shared object/object body.
            // The receiver still carries the concrete base instantiation, so recover that method
            // from the generic definition instead of comparing the shared object/object arguments.
            if (callerIsCtor && FindConcreteGenericConstructor(receiverType, candidates) is { } concreteConstructor)
            {
                instruction.SetOperand(0, concreteConstructor);
                concreteConstructor.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, concreteConstructor);
                changed = true;
                continue;
            }

            // Handle methods with shared bodies
            var match = default(MethodAnalysisContext);

            for (var type = receiverType; type != null && match == null; type = type.BaseType)
            {
                var matches = candidates.Where(c => !c.IsStatic && IsSameType(c.DeclaringType, type)).ToList();

                if (matches.Count > 1 && callerIsCtor)
                    matches = matches.Where(c => c.Name == ".ctor").ToList();

                if (matches.Count > 1)
                    break;

                match = matches.SingleOrDefault();
            }

            if (match == null)
                continue;

            instruction.SetOperand(0, match);
            match.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, match);
            changed = true;
        }

        return changed;
    }

    private static MethodAnalysisContext? FindConcreteGenericConstructor(TypeAnalysisContext receiverType, List<MethodAnalysisContext> candidates)
    {
        var candidateParameterCounts = new HashSet<int>(candidates
            .Where(c => !c.IsStatic && c.Name == ".ctor")
            .Select(c => c.Parameters.Count));

        if (candidateParameterCounts.Count == 0)
            return null;

        for (var type = receiverType; type != null; type = type.BaseType)
        {
            if (type is not GenericInstanceTypeAnalysisContext instance)
                continue;

            var matches = instance.GenericType.Methods
                .Where(m => !m.IsStatic && m.Name == ".ctor" && candidateParameterCounts.Contains(m.Parameters.Count))
                .ToList();

            if (matches is [{ } match])
                return new ConcreteGenericMethodAnalysisContext(match, instance.GenericArguments, []);
        }

        return null;
    }

    private static bool AreInterchangeable(List<MethodAnalysisContext> candidates)
    {
        var first = candidates[0];

        return candidates.All(c => c.IsStatic == first.IsStatic
            && ReferenceEquals(c.DeclaringType, first.DeclaringType)
            && ReferenceEquals(c.ReturnType, first.ReturnType)
            && c.Parameters.Count == first.Parameters.Count
            && SameParameterTypes(c, first));
    }

    private static bool SameParameterTypes(MethodAnalysisContext a, MethodAnalysisContext b)
    {
        for (var i = 0; i < a.Parameters.Count; i++)
        {
            if (!ReferenceEquals(a.Parameters[i].ParameterType, b.Parameters[i].ParameterType))
                return false;
        }

        return true;
    }

    // Prefer operators if possible
    private static MethodAnalysisContext PreferredOf(List<MethodAnalysisContext> candidates) =>
        candidates.FirstOrDefault(c => c.Name.StartsWith("op_")) ?? candidates[0];

    // The receiver ('this') of a call is the first integer-slot argument: operand 1 for CallVoid
    // (after the target), operand 2 for Call (after the target and the return value).
    // A value type receiver is passed byref, so it arrives as an AddressOf over the local.
    private static LocalVariable? GetReceiver(Instruction call, Dictionary<LocalVariable, Instruction>? definitions = null)
    {
        var index = call.OpCode == OpCode.CallVoid ? 1 : 2;

        if (index >= call.Operands.Count)
            return null;

        if (call.Operands[index] is AddressOf { Target: LocalVariable directAddressed })
            return directAddressed;

        if (call.Operands[index] is not LocalVariable local)
            return null;

        if (definitions == null)
            return local;

        // ARM64 address materialization is commonly lifted as Move local, AddressOf(local). Calls
        // then consume the pointer local instead of retaining the AddressOf wrapper. Follow local
        // copies until the addressed value is recovered, while leaving ordinary value receivers
        // untouched.
        var visited = new HashSet<LocalVariable>();
        var current = local;
        while (visited.Add(current)
               && definitions.TryGetValue(current, out var definition)
               && definition.OpCode == OpCode.Move
               && definition.Operands.Count > 1)
        {
            switch (definition.Operands[1])
            {
                case AddressOf { Target: LocalVariable aliasedAddressed }:
                    return aliasedAddressed;
                case LocalVariable next:
                    current = next;
                    continue;
                default:
                    break;
            }

            break;
        }

        return local;
    }

    // Concrete generic method contexts build their declaring type fresh rather than via the
    // GetOrCreate cache, so generic instances also need comparing structurally.
    // TODO Fix this, concrete generic methods should use GetOrCreate
    private static bool IsSameType(TypeAnalysisContext? a, TypeAnalysisContext? b)
    {
        if (ReferenceEquals(a, b))
            return true;

        if (a is not GenericInstanceTypeAnalysisContext leftInstance
            || b is not GenericInstanceTypeAnalysisContext rightInstance
            || !ReferenceEquals(leftInstance.GenericType, rightInstance.GenericType)
            || leftInstance.GenericArguments.Count != rightInstance.GenericArguments.Count)
            return false;

        for (var i = 0; i < leftInstance.GenericArguments.Count; i++)
        {
            if (!IsSameType(leftInstance.GenericArguments[i], rightInstance.GenericArguments[i]))
                return false;
        }

        return true;
    }

    /// <summary>
    /// Resolves any Call (theoretically should always be a CallVoid) target directly after a Newobj to a constructor call.
    /// </summary>
    public static bool ResolveConstructorCalls(MethodAnalysisContext method)
    {
        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
            if (instruction.Destination is LocalVariable definition)
                definitions[definition] = instruction;

        var changed = false;

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (!instruction.IsCall || instruction.Operands[0] is not Immediate callTarget)
                continue;

            if (!method.AppContext.MethodsByAddress.TryGetValue(callTarget.UnsignedValue, out var candidates))
                continue;

            if (GetReceiver(instruction, definitions) is not { } receiver || AllocatedType(receiver, definitions) is not { } allocatedType)
                continue;

            var constructor = candidates.FirstOrDefault(c => !c.IsStatic && c.Name == ".ctor" && ReferenceEquals(c.DeclaringType, allocatedType))
                              ?? FindConstructorForSharedBody(allocatedType, candidates);
            if (constructor == null)
                continue;

            instruction.SetOperand(0, constructor);
            constructor.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, constructor);
            changed = true;
        }

        return changed;
    }

    private static MethodAnalysisContext? FindConstructorForSharedBody(TypeAnalysisContext allocatedType, List<MethodAnalysisContext> candidates)
    {
        var candidateParamCounts = new HashSet<int>(candidates
            .Where(c => c is { IsStatic: false, Name: ".ctor" })
            .Select(c => c.Parameters.Count));

        if (candidateParamCounts.Count == 0)
            return null;

        var definition = allocatedType is GenericInstanceTypeAnalysisContext genericInstance ? genericInstance.GenericType : allocatedType;
        var matches = definition.Methods
            .Where(m => m is { IsStatic: false, Name: ".ctor" } && candidateParamCounts.Contains(m.Parameters.Count))
            .ToList();

        if (matches is not [{ } match])
            return null;

        return allocatedType is GenericInstanceTypeAnalysisContext instance
            ? new ConcreteGenericMethodAnalysisContext(match, instance.GenericArguments, [])
            : match;
    }

    // Follow SSA copies from a local back to the Newobj that produced the value
    private static TypeAnalysisContext? AllocatedType(LocalVariable local, Dictionary<LocalVariable, Instruction> definitions)
    {
        var visited = new HashSet<LocalVariable>();

        while (visited.Add(local) && definitions.TryGetValue(local, out var definition))
        {
            switch (definition.OpCode)
            {
                case OpCode.Newobj:
                    return (definition.Operands[0] as LocalVariable)?.Type;
                case OpCode.Move when definition.Operands[1] is LocalVariable source:
                    local = source;
                    continue;
            }

            break;
        }

        return null;
    }

    /// <summary>
    /// Resolves calls whose address maps to more than one method by reading the runtime
    /// <c>MethodInfo*</c> the caller passes in, if there is one.
    /// </summary>
    public static bool ResolveCallsViaMethodInfo(MethodAnalysisContext method)
    {
        var changed = false;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (!instruction.IsCall)
                continue;

            if (GetMethodInfoArgument(instruction) is not { RepresentedMethod: { } representedMethod })
                //No MethodInfo to work with
                continue;

            // A shared generic body can be resolved early to a single address (often the object
            // instantiation). Once the MethodInfo* argument is typed, specialize that already
            // resolved target to the concrete generic method used by the caller.
            if (instruction.Operands[0] is MethodAnalysisContext currentMethod)
            {
                if (!CanSpecializeSharedGeneric(currentMethod, representedMethod))
                    continue;

                instruction.SetOperand(0, representedMethod);
                representedMethod.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, representedMethod);
                changed = true;
                continue;
            }

            if (instruction.Operands[0] is not Immediate target)
                continue;

            if (!method.AppContext.MethodsByAddress.TryGetValue(target.UnsignedValue, out var candidates))
            {
                // A concrete generic implementation can be present in the binary metadata without
                // having a normal method candidate (for example an adjustor/thunk-only entry).
                // Restrict this fallback to addresses explicitly listed as concrete generic
                // implementations; arbitrary native/runtime calls may reuse an X1 value that looks
                // like a MethodInfo* after register allocation.
                if (!method.AppContext.Binary.ConcreteGenericImplementationsByAddress.ContainsKey(target.UnsignedValue))
                    continue;

                // Il2CPP still passes the concrete MethodInfo as the hidden final parameter, so use
                // a methodof there when available. Do not turn the caller's own MethodInfo into a
                // recursive target.
                if (ReferenceEquals(representedMethod, method))
                    continue;

                var firstArg = instruction.OpCode == OpCode.CallVoid ? 1 : 2;
                var hiddenParamIndex = firstArg
                    + (representedMethod.AppContext.InstructionSet.CallingConventionResolver?.ReturnsViaHiddenBuffer(representedMethod) == true ? 1 : 0)
                    + (representedMethod.IsStatic ? 0 : 1) + representedMethod.Parameters.Count;

                if (hiddenParamIndex >= instruction.Operands.Count
                    || AsMethodInfo(instruction.Operands[hiddenParamIndex]) == null)
                    continue;

                instruction.SetOperand(0, representedMethod);
                representedMethod.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, representedMethod);
                changed = true;
                continue;
            }

            if (candidates.Count == 1)
            {
                if (!IsSharedGenericMethod(candidates[0])
                    || !MatchesSharedGenericMethod(candidates[0], representedMethod))
                    continue;
            }
            else if (!candidates.Any(candidate => ReferenceEquals(BaseMethodOf(candidate), BaseMethodOf(representedMethod))))
            {
                continue;
            }

            //Try to actually match on the method name so we don't just replace a call with something else.
            instruction.SetOperand(0, representedMethod);
            representedMethod.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, representedMethod);
            changed = true;
        }

        return changed;
    }

    private static bool CanSpecializeSharedGeneric(MethodAnalysisContext current, MethodAnalysisContext represented)
    {
        if (ReferenceEquals(current, represented)
            || current.Name != represented.Name
            || current.Parameters.Count != represented.Parameters.Count
            || current.DeclaringType is not GenericInstanceTypeAnalysisContext currentInstance
            || represented.DeclaringType is not GenericInstanceTypeAnalysisContext representedInstance
            || !IsSameType(currentInstance.GenericType, representedInstance.GenericType)
            || IsSameType(current.DeclaringType, represented.DeclaringType))
            return false;

        var currentBase = BaseMethodOf(current);
        var representedBase = BaseMethodOf(represented);
        return ReferenceEquals(currentBase, representedBase)
               || (currentBase.Name == representedBase.Name
                   && currentBase.Parameters.Count == representedBase.Parameters.Count
                   && IsSameType(currentBase.DeclaringType, representedBase.DeclaringType));
    }

    private static bool IsSharedGenericMethod(MethodAnalysisContext method)
    {
        if (method.DeclaringType is not GenericInstanceTypeAnalysisContext instance
            || instance.GenericArguments.Count == 0)
            return false;

        // IL2CPP uses System.Object as the canonical body for reference-type generic sharing.
        return instance.GenericArguments.Any(argument => argument == method.AppContext.SystemTypes.SystemObjectType);
    }

    private static bool MatchesSharedGenericMethod(MethodAnalysisContext shared, MethodAnalysisContext represented)
    {
        if (!IsSharedGenericMethod(shared)
            || shared.Name != represented.Name
            || shared.IsStatic != represented.IsStatic
            || shared.Parameters.Count != represented.Parameters.Count)
            return false;

        if (ReferenceEquals(BaseMethodOf(shared), BaseMethodOf(represented)))
            return true;

        return shared.DeclaringType is GenericInstanceTypeAnalysisContext sharedInstance
            && represented.DeclaringType is GenericInstanceTypeAnalysisContext representedInstance
            && ReferenceEquals(sharedInstance.GenericType, representedInstance.GenericType)
            && sharedInstance.GenericArguments.Count == representedInstance.GenericArguments.Count;
    }

    private static MethodAnalysisContext? TrySpecializeSharedGeneric(MethodAnalysisContext shared, TypeAnalysisContext receiverType)
    {
        if (!IsSharedGenericMethod(shared)
            || shared.DeclaringType is not GenericInstanceTypeAnalysisContext sharedInstance)
            return null;

        for (var type = receiverType; type != null; type = type.BaseType)
        {
            if (type is not GenericInstanceTypeAnalysisContext receiverInstance
                || !ReferenceEquals(receiverInstance.GenericType, sharedInstance.GenericType)
                || receiverInstance.GenericArguments.Count != sharedInstance.GenericArguments.Count)
                continue;

            // The canonical object body is already the right target for an object receiver.
            var sameArguments = true;
            for (var i = 0; i < receiverInstance.GenericArguments.Count; i++)
            {
                if (IsSameType(receiverInstance.GenericArguments[i], sharedInstance.GenericArguments[i]))
                    continue;

                sameArguments = false;
                break;
            }

            if (sameArguments)
                return shared;

            var matches = receiverInstance.GenericType.Methods
                .Where(candidate => candidate.Name == shared.Name
                    && candidate.IsStatic == shared.IsStatic
                    && candidate.Parameters.Count == shared.Parameters.Count)
                .ToList();

            if (matches is not [{ } definition]
                || definition.DeclaringType?.GenericParameters.Count != receiverInstance.GenericArguments.Count
                || definition.GenericParameters.Count != shared.GenericParameters.Count)
                return null;

            // Shared generic methods with their own method parameters need a second instantiation
            // source which is not available on this edge; leave those unresolved.
            if (definition.GenericParameters.Count != 0)
                return null;

            return new ConcreteGenericMethodAnalysisContext(definition, receiverInstance.GenericArguments, []);
        }

        return null;
    }

    // Offset of Il2CppClass::vtable, VirtualInvokeData entries of {methodPtr, MethodInfo*}.
    // TODO this is almost certainly not correct on every version
    private const long VTableOffset64 = 0x138;
    private const long VTableOffset32 = 0xC0;
    
    // Resolves virtual dispatch through <c>[klass + vtableOffset + slot * sizeof(VirtualInvokeData)]</c>
    // as long as the klass local's represented type is known. Handles both a normal call and a tail
    // call, which the lifter leaves as an IndirectJump.
    public static bool ResolveVirtualCalls(MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var vtableOffset = pointerSize == 8 ? VTableOffset64 : VTableOffset32;
        var invokeDataSize = 2L * pointerSize;
        var changed = false;

        var loads = new Dictionary<LocalVariable, MemoryOperand>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode == OpCode.Move
                && instruction.Operands[0] is LocalVariable destination
                && instruction.Operands[1] is MemoryOperand { Index: null, Scale: 0 } load)
                loads[destination] = load;
        }

        foreach (var block in method.ControlFlowGraph.Blocks.ToList())
        {
            foreach (var instruction in block.Instructions.ToList())
            {
                if (instruction.OpCode is not (OpCode.IndirectCall or OpCode.IndirectJump))
                    continue;

                if (SlotLoad(instruction.Operands[0]) is not { } target
                    || target.Base is not LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: { } receiverType } } klassLocal)
                    continue;

                var offset = target.Addend - vtableOffset;
                if (offset < 0 || offset % invokeDataSize != 0)
                    continue;

                var slot = (int)(offset / invokeDataSize);
                if (ResolveVTableSlot(method.AppContext, receiverType, slot) is not { } resolved)
                    continue;

                var assembly = resolved.DeclaringType?.DeclaringAssembly ?? method.DeclaringType?.DeclaringAssembly;
                var isTailCall = instruction.OpCode == OpCode.IndirectJump;
                var callingConventions = resolved.AppContext.InstructionSet.CallingConventionResolver;

                if (isTailCall)
                {
                    // an IndirectJump's return register operand is a stale use rather than a return
                    // slot, so rebuild the operand list around the resolved signature
                    var operands = new List<IOperand> { resolved };

                    if (!resolved.IsVoid)
                        operands.Add(new LocalVariable("virtualTailCallResult", callingConventions?.ReturnRegister(resolved) ?? new Register(null, "rax")));

                    operands.AddRange(instruction.Operands.Skip(2));
                    instruction.SetOperands(operands);
                    instruction.OpCode = resolved.IsVoid ? OpCode.CallVoid : OpCode.Call;
                }
                else
                {
                    instruction.OpCode = resolved.IsVoid ? OpCode.CallVoid : OpCode.Call;
                    instruction.SetOperand(0, resolved);

                    if (resolved.IsVoid)
                        instruction.RemoveOperandAt(1);
                    else if (callingConventions is { }
                             && instruction.ImplicitDefinition is { } returnDefinition
                             && returnDefinition.Number == callingConventions.ReturnRegister(resolved).Number
                             && method.Locals.FirstOrDefault(local => local.Register == returnDefinition) is { } floatResult)
                        instruction.SetOperand(1, floatResult);
                }

                resolved.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, resolved);

                // the MethodInfo field is also the same method, name it, for cleanliness and so it can
                // serve as a hidden final parameter if needed
                for (var i = 1; i < instruction.Operands.Count && assembly != null; i++)
                {
                    if (SlotLoad(instruction.Operands[i]) is { } methodInfoLoad
                        && ReferenceEquals(methodInfoLoad.Base, klassLocal)
                        && methodInfoLoad.Addend == target.Addend + pointerSize)
                        instruction.SetOperand(i, new RuntimeMethodInfoAnalysisContext(resolved, assembly));
                }

                if (isTailCall)
                {
                    // the jump was the block's terminator, so the call now needs an explicit return
                    var returnOperands = !method.IsVoid && !resolved.IsVoid
                        ? new List<IOperand> { instruction.Operands[1] }
                        : [];

                    block.AddInstruction(new Instruction(-1, OpCode.Return, returnOperands));
                    block.CalculateBlockType();
                }

                changed = true;
            }
        }

        return changed;

        MemoryOperand? SlotLoad(IOperand operand) => operand switch
        {
            MemoryOperand { Index: null, Scale: 0 } inlined => inlined,
            LocalVariable local when loads.TryGetValue(local, out var load) => load,
            _ => null
        };
    }

    private static MethodAnalysisContext? ResolveVTableSlot(ApplicationAnalysisContext appContext, TypeAnalysisContext type, int slot)
    {
        var definition = (type as GenericInstanceTypeAnalysisContext)?.GenericType.Definition ?? type.Definition;

        if (definition == null || slot >= definition.VtableCount)
            return null;

        if (appContext.ResolveContextForMethod(definition.VTable[slot]) is { } implementation)
            return implementation;

        // an abstract method has no implementation, try to resolve it
        for (var declarer = type; declarer != null; declarer = declarer.BaseType)
        {
            if (declarer.Methods.FirstOrDefault(m => m.Definition?.slot == slot) is { } declaration)
                return declaration;
        }

        return null;
    }

    private static MethodAnalysisContext BaseMethodOf(MethodAnalysisContext method) =>
        method is ConcreteGenericMethodAnalysisContext { BaseMethodContext: { } baseMethod } ? baseMethod : method;

    private static RuntimeMethodInfoAnalysisContext? GetMethodInfoArgument(Instruction call)
    {
        var firstArg = call.OpCode == OpCode.CallVoid ? 1 : 2;

        for (var i = call.Operands.Count - 1; i >= firstArg; i--)
        {
            if (AsMethodInfo(call.Operands[i]) is { } methodInfo)
                return methodInfo;
        }

        return null;
    }

    private static RuntimeMethodInfoAnalysisContext? AsMethodInfo(IOperand operand) =>
        operand switch
        {
            RuntimeMethodInfoAnalysisContext methodInfo => methodInfo,
            LocalVariable { Type: RuntimeMethodInfoAnalysisContext methodInfoLocal } => methodInfoLocal,
            _ => null
        };

    private static void HandleKeyFunction(ApplicationAnalysisContext appContext, Instruction instruction, ulong target, BaseKeyFunctionAddresses kFA)
    {
        var method = "";
        if (target == kFA.il2cpp_codegen_initialize_method || target == kFA.il2cpp_codegen_initialize_runtime_metadata)
        {
            if (appContext.MetadataVersion < 27)
            {
                method = nameof(kFA.il2cpp_codegen_initialize_method);
            }
            else
            {
                method = nameof(kFA.il2cpp_codegen_initialize_runtime_metadata);
            }
        }
        else
        {
            var pairs = kFA.Pairs.ToList();
            var key = pairs.FirstOrDefault(pair => pair.Value == target).Key;
            if (key == null)
                return;
            method = key;
        }

        if (method != "")
        {
            instruction.SetOperand(0, new StringLiteral(method));
        }
    }

    // Because of il2cpp fields (like cctor_finished_or_no_cctor) [local @ reg+offset] sometimes can't be resolved, but this works for now
    private static void ResolveGetter(MethodAnalysisContext method)
    {
        if (!method.Name.StartsWith("get_"))
            return;

        // Default get: Return [this @ reg+offset]
        var instructions = method.ControlFlowGraph!.Instructions;
        if (instructions.Count == 1)
        {
            var instr = instructions[0];

            if (instr.OpCode != OpCode.Return
                || instr.Operands.Count < 1
                || instr.Operands[0] is not MemoryOperand memory
                || memory.Index != null || memory.Scale != 0
                || memory.Base is not LocalVariable local)
                return;

            var fieldName = $"<{method.Name[4..]}>k__BackingField";

            var field = method.DeclaringType!.Fields.Find(f => f.Name == fieldName);
            if (field == null)
                return;

            instr.SetOperand(0, new FieldReference(field, local, (int)memory.Addend));
        }
    }
}
