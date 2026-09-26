using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using Disarm;
using Disarm.InternalDisassembly;
using LibCpp2IL;
using LibCpp2IL.BinaryStructures;

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
    internal static void ResolveMetadataUsages(MethodAnalysisContext method)
    {
        var libContext = method.AppContext.LibCpp2IlContext;
        var resolvedMetadataPointers = new Dictionary<LocalVariable, IOperand>();

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Move)
                continue;

            if (instruction.Operands[0] is not LocalVariable destination)
                continue;

            if (instruction.Operands[1] is TypeAnalysisContext or StringLiteral)
            {
                resolvedMetadataPointers[destination] = instruction.Operands[1];
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
        ResolveIndirectMetadataUsages(method.ControlFlowGraph.Instructions, resolvedMetadataPointers);
    }

    // SSA block order is not definition order. Carry known metadata slots through
    // copies and unanimous phis before resolving their zero-offset loads.
    internal static void ResolveIndirectMetadataUsages(IEnumerable<Instruction> instructions, Dictionary<LocalVariable, IOperand> resolved)
    {
        var pending = instructions.Where(i => i.OpCode is OpCode.Move or OpCode.Phi
            && i.Destination is LocalVariable).ToList();
        var definitions = pending.GroupBy(i => (LocalVariable)i.Destination!)
            .ToDictionary(g => g.Key, g => g.Count() == 1 ? g.Single() : null);
        bool changed;
        do
        {
            changed = false;
            foreach (var instruction in pending)
            {
                var destination = (LocalVariable)instruction.Destination!;
                if (resolved.ContainsKey(destination)) continue;
                IOperand? value = null;
                if (instruction is { OpCode: OpCode.Move, Operands: [_, LocalVariable source] })
                    resolved.TryGetValue(source, out value);
                else if (instruction is { OpCode: OpCode.Move, Operands: [_, MemoryOperand
                    { Base: LocalVariable pointer, Index: null, Scale: 0, Addend: 0 }] })
                {
                    if (!resolved.ContainsKey(pointer))
                        ResolveMetadataCopyCycle(pointer, definitions, resolved);
                    if (resolved.TryGetValue(pointer, out value)) instruction.SetOperand(1, value);
                }
                else if (instruction.OpCode == OpCode.Phi && instruction.Operands.Count > 1)
                {
                    foreach (var operand in instruction.Operands.Skip(1))
                    {
                        if (operand is not LocalVariable input || !resolved.TryGetValue(input, out var incoming)
                            || value != null && !Equals(value, incoming))
                        { value = null; break; }
                        value = incoming;
                    }
                }
                if (value == null) continue;
                resolved[destination] = value;
                changed = true;
            }
        } while (changed);
    }

    // A loop phi can depend on itself through several copies. Prove its entire copy
    // graph has one metadata seed; waiting for every backedge to resolve cannot converge.
    // Unknown leaves, computations and disagreeing seeds invalidate the whole proof.
    private static void ResolveMetadataCopyCycle(LocalVariable root,
        Dictionary<LocalVariable, Instruction?> definitions, Dictionary<LocalVariable, IOperand> resolved)
    {
        var pending = new Stack<IOperand>();
        var visited = new HashSet<LocalVariable>();
        IOperand? seed = null;
        pending.Push(root);
        while (pending.TryPop(out var operand))
        {
            if (operand is LocalVariable local)
            {
                if (resolved.TryGetValue(local, out var known)) operand = known;
                else
                {
                    if (!visited.Add(local)) continue;
                    if (visited.Count > 1024 || !definitions.TryGetValue(local, out var definition)
                        || definition is not { OpCode: OpCode.Move or OpCode.Phi, Operands.Count: > 1 }) return;
                    foreach (var source in definition.Operands.Skip(1)) pending.Push(source);
                    continue;
                }
            }
            if (operand is not (TypeAnalysisContext or StringLiteral) || seed != null && !Equals(seed, operand)) return;
            seed = operand;
        }
        if (seed == null) return;
        // Every subcycle needs an incoming seed of its own. A seeded outer phi must
        // not give an otherwise uninitialized inner cycle a fabricated value.
        var anchored = new HashSet<LocalVariable>();
        bool changed;
        do
        {
            changed = false;
            foreach (var local in visited)
                if (!anchored.Contains(local) && definitions[local]!.Operands.Skip(1).Any(source =>
                    source is TypeAnalysisContext or StringLiteral
                    || source is LocalVariable input && (resolved.ContainsKey(input) || anchored.Contains(input))))
                    changed |= anchored.Add(local);
        } while (changed);
        if (anchored.Count != visited.Count) return;
        foreach (var local in visited) resolved[local] = seed;
    }

    /// <summary>
    /// Replaces every <c>[base + addend]</c> memory operand whose base is a typed local with a
    /// <see cref="FieldReference"/> to the field at that offset. Returns whether any operand was
    /// resolved this pass, so the type/field fixpoint can detect convergence: as more bases become
    /// typed (a field load types its result, which is the base of the next load), more offsets
    /// resolve, so this is re-run until it stops finding new fields.
    /// </summary>
    public static bool ResolveFieldOffsets(MethodAnalysisContext method, bool deferUntypedStores = false)
    {
        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
            if (instruction.Destination is LocalVariable destination)
                definitions[destination] = instruction;

        // A by-value struct may arrive in several native registers. Its first load
        // must remain an aggregate when a typed consumer (possibly through copies)
        // expects the full value, even if that individual access is narrower.
        var aggregateCopies = new HashSet<LocalVariable>();
        var pendingAggregates = new Queue<LocalVariable>(definitions.Keys.Where(v => IsAggregate(v.Type)));
        while (pendingAggregates.TryDequeue(out var aggregate))
            if (aggregateCopies.Add(aggregate) && definitions.TryGetValue(aggregate, out var copy)
                && copy.OpCode is OpCode.Move or OpCode.Phi)
                foreach (var source in copy.Sources.OfType<LocalVariable>())
                    pendingAggregates.Enqueue(source);

        static bool IsAggregate(TypeAnalysisContext? type) => type is ByRefTypeAnalysisContext byRef
            ? IsAggregate(byRef.ElementType)
            : type is { IsValueType: true, IsEnumType: false, Type: Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE or Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST };

        // Frame slots whose address escapes hold their struct in place (a return buffer, a ref argument).
        var addressedSlots = method.ControlFlowGraph!.Instructions.SelectMany(i => i.Operands)
            .OfType<AddressOf>().Select(a => a.Target).OfType<LocalVariable>().Where(IsFrameSlot).ToHashSet();

        var changed = false;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                var operand = instruction.Operands[i];

                // A memory-to-memory Move is the folded form of a native aggregate copy
                // (for example, an 8-byte Vector2 assignment). At zero offset this address
                // is not a scalar field access; preserve the aggregate copy instead of reducing it to the first member.
                if (instruction.OpCode == OpCode.Move
                    && instruction.Operands.Count == 2
                    && instruction.Operands[0] is MemoryOperand
                    && instruction.Operands[1] is MemoryOperand)
                    continue;

                // Before SSA elimination, aggregate copies appear as a 64-bit X-register temporary
                // between two byref accesses. Resolving either end as Vector2.x would lose the adjacent
                // y component when the temporary is inlined, so preserve the original copy.
                if (operand is MemoryOperand aggregateMemory
                    && IsByRefValueAggregateCopy(instruction, i, aggregateMemory))
                    continue;

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

                if (!MergedBaseAgrees(fieldLocal, fieldOffset, definitions))
                    continue;

                // A register copied from a value-type field holds (the first bytes of) the value, not
                // its address. Dereferencing it reads through the value's first member, e.g. the
                // object header of UniTask<T>.Awaiter.task.source, never a member of the struct.
                // A frame slot used as a base addresses the struct stored in it, so only registers apply.
                if (fieldLocal.Type is { IsValueType: true } and not ByRefTypeAnalysisContext && !IsFrameSlot(fieldLocal)
                    && definitions.ContainsKey(fieldLocal) && HoldsValueTypeValue(fieldLocal, definitions, addressedSlots, []))
                    continue;

                // check if static field access
                var staticOwner = (fieldLocal.Type as StaticFieldStorageTypeAnalysisContext)?.OwnerType;
                var owner = staticOwner ?? fieldLocal.Type;
                // A ref/out parameter points at the managed value, so resolve offsets against the
                // referent's fields rather than the ByRef wrapper itself.
                if (owner is ByRefTypeAnalysisContext byRef)
                    owner = byRef.ElementType;
                var genericOwner = owner as GenericInstanceTypeAnalysisContext;
                GenericInstanceTypeAnalysisContext? fieldGenericOwner = genericOwner;

                // Search the complete inheritance chain. Generic base classes have zero metadata
                // offsets, so compute their instantiated layout and retain the concrete owner for
                // field type substitution (e.g. ResourcePool<AreaObjectCharacter>.resources).
                FieldAnalysisContext? field = null;
                if (fieldLocal.Type is StaticFieldStorageTypeAnalysisContext { IsThreadStatic: true })
                {
                    // The high bit encodes thread-static storage, not part of its byte offset.
                    // Generic and embedded layouts without an exact field match stay unresolved.
                    if (genericOwner != null || fieldOffset < 0 || fieldOffset >= int.MaxValue)
                        continue;
                    var encodedOffset = unchecked((int)((uint)fieldOffset | 0x80000000u));
                    field = owner.Fields.FirstOrDefault(f => f.IsStatic && f.Offset == encodedOffset
                        && (f.Attributes & FieldAttributes.Literal) == 0);
                    if (field == null)
                        continue;
                }
                if (staticOwner is GenericInstanceTypeAnalysisContext staticGeneric)
                {
                    // Instantiations do not populate Fields and generic definitions can report every
                    // offset as zero, so the instantiated static layout is computed instead.
                    field = StaticFieldAtOffset(staticGeneric.GenericType, fieldOffset, method.AppContext.Binary.PointerSizeBytes);
                    if (field == null)
                        continue;
                }
                for (var candidateOwner = owner; candidateOwner != null && field == null; candidateOwner = candidateOwner.BaseType)
                {
                    // Substitute against the field's declaring base, not the receiver's type.
                    fieldGenericOwner = candidateOwner as GenericInstanceTypeAnalysisContext;
                    if (staticOwner == null && candidateOwner is GenericInstanceTypeAnalysisContext candidateGeneric)
                    {
                        field = GenericInstanceFieldLayout.FindFieldAtOffset(candidateGeneric, fieldOffset);
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

                // Value-type fields that enclose the accessed member, outermost first.
                IReadOnlyList<FieldAnalysisContext> containingFields = [];
                if (field == null)
                {
                    // A pair load/store can address a member inside an embedded value type, e.g.
                    // Vector2.y at outerFieldOffset + 4, or Bounds.m_Extents.z two levels down.
                    // Resolve the innermost field so IL generation can use ldflda/stfld instead of
                    // leaving an untyped raw memory access behind.
                    // Static storage holds only its own type's statics, so a static containing field
                    // (Vector3.oneVector.y) is searched on the owner alone, never on its base types.
                    for (var candidateOwner = owner;
                         candidateOwner != null && field == null;
                         candidateOwner = staticOwner == null ? candidateOwner.BaseType : null)
                    {
                        // Generic definition offsets are placeholders, so a generic owner or a
                        // generic value-type field is searched through its computed layout instead.
                        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
                        var embedded = IsComputedLayout(candidateOwner)
                            ? null
                            : FindEmbeddedMember(candidateOwner, fieldOffset, staticOwner != null, memory.AccessSize, pointerSize);
                        embedded ??= FindComputedEmbeddedMember(candidateOwner, fieldOffset, staticOwner != null, memory.AccessSize, pointerSize);
                        if (embedded is var (chain, nested))
                            (containingFields, field) = (chain, nested);
                    }

                    if (field == null)
                    {
                        if (staticOwner == null && TrySplitZeroStore(method, instruction, i, owner, fieldLocal, fieldOffset, memory.AccessSize))
                            changed = true;
                        continue;
                    }
                }

                // Bind the containing field before inspecting its members, so nested stores
                // preserve both the substituted field type and the concrete declaring owner.
                if (fieldGenericOwner != null && containingFields.Count == 0)
                    field = new ConcreteGenericFieldAnalysisContext(field, fieldGenericOwner);

                // Width is evidence for a partial access only if a later member proves the
                // aggregate extends beyond it. Equal-sized whole-struct copies stay intact.
                if (instruction.OpCode == OpCode.Move
                    && (i == 1 && instruction.Destination is LocalVariable result && !aggregateCopies.Contains(result)
                        || i == 0 && (instruction.Operands[1] is Immediate
                            || OperandType(instruction.Operands[1], method, definitions) is { } sourceType && !IsAggregate(sourceType))
                            && !(instruction.Operands[1] is LocalVariable source && aggregateCopies.Contains(source)))
                    && memory.AccessSize > 0
                    && ResolvePartialStructAccess(field, fieldLocal, (int)fieldOffset, memory.AccessSize,
                        method.AppContext.Binary.PointerSizeBytes, containingFields) is { } scalar)
                {
                    instruction.SetOperand(i, scalar);
                    changed = true;
                    continue;
                }

                // A store narrower than the struct field it starts, of a value not yet typed, waits for the
                // value's type: the whole field's type would otherwise flow back onto the value from this very
                // store, and the first-member choice below could never be made. What never gets a type is
                // resolved once type propagation settles.
                if (deferUntypedStores && instruction.OpCode == OpCode.Move && i == 0 && field.FieldType is { IsValueType: true } fieldType
                    && IsAggregate(fieldType) && memory.AccessSize > 0
                    && instruction.Operands[1] is LocalVariable { Type: null } untypedValue && !aggregateCopies.Contains(untypedValue)
                    && memory.AccessSize < TypeSizes.UnboxedSize(fieldType, method.AppContext.Binary.PointerSizeBytes))
                    continue;

                var resolved = new FieldReference(field, fieldLocal, (int)fieldOffset)
                    { ContainingFields = containingFields, AccessSize = memory.AccessSize };

                // A scalar store at the start of an embedded value type is a store to its first
                // member, not an assignment of the whole aggregate (e.g. Vector2.x). The native
                // compiler commonly emits this shape when initializing one component separately.
                if (instruction.OpCode == OpCode.Move
                    && i == 0
                    && field.FieldType.IsValueType
                    && OperandType(instruction.Operands[1], method, definitions) is { } storedType
                    && field.FieldType.FullName != storedType.FullName
                    && field.FieldType.Fields.FirstOrDefault(n => !n.IsStatic && n.Offset == 0
                        && n.FieldType.FullName == storedType.FullName) is { } firstMember)
                {
                    resolved = new FieldReference(firstMember, fieldLocal, (int)fieldOffset)
                        { ContainingFields = [.. containingFields, field] };
                }

                instruction.SetOperand(i, resolved);
                changed = true;
            }
        }

        return changed;
    }

    /// <summary>
    /// Finds the member at <paramref name="offset"/> inside one of <paramref name="owner"/>'s value-type
    /// fields. A member directly inside a field (Vector2.y) resolves as it always has; otherwise the
    /// search descends through nested value types (Bounds.m_Extents.z), where each level must be the
    /// unique non-generic struct field whose unboxed size covers the offset and the member must not
    /// be narrower than a known <paramref name="accessSize"/>, so an 8-byte pair is never read as
    /// its first 4-byte member.
    /// </summary>
    private static (IReadOnlyList<FieldAnalysisContext> Chain, FieldAnalysisContext Member)? FindEmbeddedMember(
        TypeAnalysisContext owner, long offset, bool isStatic, int accessSize, int pointerSize)
    {
        var fields = owner.Fields.Where(f => f.IsStatic == isStatic
            && (f.Attributes & FieldAttributes.Literal) == 0).ToList();

        var direct = fields.FirstOrDefault(f => f.FieldType.IsValueType
            && f.Offset >= 0
            && f.FieldType.Fields.Any(n => !n.IsStatic && n.Offset == offset - f.Offset));
        if (direct?.FieldType.Fields.FirstOrDefault(n => !n.IsStatic && n.Offset == offset - direct.Offset) is { } directMember)
            return ([direct], directMember);

        var chain = new List<FieldAnalysisContext>();
        var candidates = fields;
        var relative = offset;
        while (true)
        {
            // Only plain structs are containers: primitives wrap themselves (Single.m_value) and
            // enums only wrap their underlying value.
            var containing = candidates.Where(f => f.FieldType is { Type: Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE, IsEnumType: false }
                && f.Offset >= 0 && f.Offset < relative
                && relative - f.Offset < TypeSizes.UnboxedSize(f.FieldType, pointerSize)).ToList();
            if (containing is not [{ } parent] || parent.FieldType.GenericParameters.Count > 0)
                return null;

            chain.Add(parent);
            relative -= parent.Offset;
            candidates = parent.FieldType.Fields.Where(f => !f.IsStatic).ToList();
            if (chain.Count > 1 && candidates.Where(f => f.Offset == relative).ToList() is [{ } member])
            {
                var size = TypeSizes.UnboxedSize(member.FieldType, pointerSize);
                return accessSize > 0 && member.FieldType.IsValueType && size > 0 && size < accessSize
                    && !OnlyPaddingFollows(MemberSlots(parent.FieldType, false, pointerSize), relative, size, accessSize,
                        TypeSizes.UnboxedSize(parent.FieldType, pointerSize))
                    ? null
                    : (chain, member);
            }
        }
    }

    /// <summary>
    /// Finds the member at <paramref name="offset"/> when the path to it runs through a layout that
    /// metadata does not record: a generic owner, or a containing field of a generic value type such as
    /// <c>UniTask&lt;T&gt;.Awaiter.task.result</c>. Each level must be the unique value-type field
    /// covering the offset in the computed layout, and the member must span the access apart from
    /// trailing padding. Paths without a computed layout are left to <see cref="FindEmbeddedMember"/>.
    /// </summary>
    private static (IReadOnlyList<FieldAnalysisContext> Chain, FieldAnalysisContext Member)? FindComputedEmbeddedMember(
        TypeAnalysisContext owner, long offset, bool isStatic, int accessSize, int pointerSize)
    {
        var computed = IsComputedLayout(owner);
        var slots = MemberSlots(owner, isStatic, pointerSize);
        var chain = new List<FieldAnalysisContext>();
        var relative = offset;
        while (slots != null)
        {
            var containing = slots.Where(s => IsValueContainer(s.Field.FieldType)
                && s.Offset < relative && relative < s.Offset + s.Size).ToList();
            if (containing is not [{ } parent])
                return null;

            chain.Add(parent.Field);
            relative -= parent.Offset;
            computed |= IsComputedLayout(parent.Field.FieldType);
            slots = MemberSlots(parent.Field.FieldType, false, pointerSize);
            if (slots?.Where(s => s.Offset == relative).ToList() is [{ } member])
            {
                if (!computed || member.Size <= 0)
                    return null;
                return accessSize <= member.Size || OnlyPaddingFollows(slots, relative, member.Size, accessSize, parent.Size)
                    ? (chain, member.Field)
                    : null;
            }
        }

        return null;
    }

    /// <summary>
    /// Whether <paramref name="local"/> receives a value-type value, through moves and phis:
    /// a by-value copy of a field, a call result returned in registers, or the contents of a frame
    /// slot holding the struct in place. Such a register holds the value itself. A pointer to the
    /// struct (this, a return buffer, a by-reference argument or a spilled copy of one) comes from none of them.
    /// </summary>
    private static bool HoldsValueTypeValue(LocalVariable local, Dictionary<LocalVariable, Instruction> definitions,
        HashSet<LocalVariable> addressedSlots, HashSet<LocalVariable> visited)
    {
        if (!visited.Add(local))
            return false;
        // A value-type frame slot whose address is taken holds the struct itself, written in place by
        // a call's return buffer or through a ref argument; loading from it copies (part of) the value.
        if (addressedSlots.Contains(local) && local.Type is { IsValueType: true } and not ByRefTypeAnalysisContext)
            return true;
        if (!definitions.TryGetValue(local, out var definition))
            return false;
        return definition switch
        {
            { OpCode: OpCode.Move, Operands: [_, FieldReference { Field.FieldType.IsValueType: true }] } => true,
            { OpCode: OpCode.Call, Destination: LocalVariable { Type: { IsValueType: true } and not ByRefTypeAnalysisContext } } => true,
            { OpCode: OpCode.Move, Operands: [_, LocalVariable source] } => HoldsValueTypeValue(source, definitions, addressedSlots, visited),
            // A register cannot hold a struct on one path and its address on another; an incoming
            // value without a definition (an uninitialised stack slot version) decides nothing.
            { OpCode: OpCode.Phi } => definition.Operands.Skip(1)
                .Any(o => o is LocalVariable incoming && HoldsValueTypeValue(incoming, definitions, addressedSlots, visited)),
            _ => false
        };
    }

    private static bool IsFrameSlot(LocalVariable local) => local.Register.Name is { } name
        && (name.StartsWith("stack_", StringComparison.Ordinal) || name.StartsWith("aggregate_stack_", StringComparison.Ordinal));

    /// <summary>
    /// The static field of a generic type at <paramref name="offset"/> in its static storage. IL2CPP lays static
    /// fields out like instance ones: in declaration order, each at its natural alignment. That is known for
    /// every instantiation when no static field's size depends on a type argument (a reference or a
    /// non-generic struct), which covers lambda caches such as &lt;&gt;c__8&lt;A, B&gt;.
    /// </summary>
    private static FieldAnalysisContext? StaticFieldAtOffset(TypeAnalysisContext definition, long offset, int pointerSize)
    {
        var current = 0L;
        foreach (var field in definition.Fields.Where(f => f.IsStatic && (f.Attributes & FieldAttributes.Literal) == 0))
        {
            // Thread statics live in separate storage and carry an encoded offset.
            if (field.Offset < 0)
                return null;
            var type = field.FieldType;
            long size, alignment;
            if (type is GenericParameterTypeAnalysisContext or ByRefTypeAnalysisContext)
                return null;
            if (!type.IsValueType || type is PointerTypeAnalysisContext)
                (size, alignment) = (pointerSize, pointerSize);
            else if (type is not GenericInstanceTypeAnalysisContext && GenericInstanceFieldLayout.ValueTypeSizeAndAlignment(type) is var (valueSize, valueAlignment))
                (size, alignment) = (valueSize, valueAlignment);
            else
                return null;
            if (size <= 0 || alignment <= 0)
                return null;
            current = (current + alignment - 1) / alignment * alignment;
            if (current == offset)
                return field;
            if (current > offset)
                return null;
            current += size;
        }
        return null;
    }

    /// <summary>
    /// A zero store wider than the member at its offset clears several adjacent members of one embedded
    /// value type at once, e.g. the result and token of an awaiter being reset to default. When it covers
    /// those members exactly (padding aside) and cuts none of them, split it into a zero store to each.
    /// </summary>
    private static bool TrySplitZeroStore(MethodAnalysisContext method, Instruction store, int operandIndex, TypeAnalysisContext owner,
        LocalVariable fieldLocal, long offset, int accessSize)
    {
        if (operandIndex != 0 || accessSize <= 0 || store is not { OpCode: OpCode.Move, Operands: [MemoryOperand, Immediate { Value: 0 }] }
            || IsComputedLayout(owner)
            || method.ControlFlowGraph!.Blocks.FirstOrDefault(b => b.Instructions.Contains(store)) is not { } block)
            return false;

        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var slots = MemberSlots(owner, false, pointerSize);
        var chain = new List<FieldAnalysisContext>();
        var relative = offset;
        while (slots != null)
        {
            // The value-type field holding the whole store, then what the store covers inside it.
            if (slots.Where(s => IsValueContainer(s.Field.FieldType) && s.Size > 0
                    && s.Offset <= relative && relative + accessSize <= s.Offset + s.Size).ToList() is not [{ } parent])
                return false;
            chain.Add(parent.Field);
            relative -= parent.Offset;
            slots = MemberSlots(parent.Field.FieldType, false, pointerSize);
            if (slots == null)
                return false;

            var covered = slots.Where(s => s.Offset < relative + accessSize && s.Offset + s.Size > relative).ToList();
            if (covered.Count < 2)
                continue; // inside a single member: descend into it if it is a struct
            if (covered.Any(s => s.Size <= 0 || s.Offset < relative || s.Offset + s.Size > relative + accessSize))
                return false;

            var baseOffset = offset - relative;
            var stores = covered.Select(member => new Instruction(-1, OpCode.Move,
                new FieldReference(member.Field, fieldLocal, (int)(baseOffset + member.Offset))
                    { ContainingFields = chain.ToArray(), AccessSize = (int)member.Size },
                new Immediate(0)) { NativeAddress = store.NativeAddress }).ToList();
            store.SetOperand(0, stores[0].Operands[0]);
            block.Instructions.InsertRange(block.Instructions.IndexOf(store) + 1, stores.Skip(1));
            return true;
        }

        return false;
    }

    private static bool IsComputedLayout(TypeAnalysisContext type)
        => type is GenericInstanceTypeAnalysisContext || type.GenericParameters.Count > 0;

    // Only plain structs contain members: primitives wrap themselves (Single.m_value) and enums
    // only wrap their underlying value.
    private static bool IsValueContainer(TypeAnalysisContext type)
        => type is { Type: Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE, IsEnumType: false }
            or GenericInstanceTypeAnalysisContext { IsValueType: true, IsEnumType: false };

    /// <summary>
    /// The fields of <paramref name="type"/> at their offsets. Metadata offsets are authoritative for a
    /// non-generic type; a generic definition or instance, whose metadata offsets are placeholders,
    /// uses its computed layout with fields bound to the instantiation. A size of 0 is unknown.
    /// </summary>
    private static List<GenericInstanceFieldLayout.FieldSlot>? MemberSlots(TypeAnalysisContext type, bool isStatic, int pointerSize)
    {
        if (IsComputedLayout(type))
            return isStatic ? null : GenericInstanceFieldLayout.ComputeLayout(type)?.Slots;
        return type.Fields.Where(f => f.IsStatic == isStatic && (f.Attributes & FieldAttributes.Literal) == 0 && f.Offset >= 0)
            .Select(f => new GenericInstanceFieldLayout.FieldSlot(f, f, f.Offset, FieldSize(f.FieldType, pointerSize)))
            .ToList();
    }

    private static long FieldSize(TypeAnalysisContext type, int pointerSize)
        => type is GenericParameterTypeAnalysisContext or PointerTypeAnalysisContext || !type.IsValueType ? pointerSize
            : GenericInstanceFieldLayout.ValueTypeSizeAndAlignment(type) is { } layout ? layout.Size
            : type is GenericInstanceTypeAnalysisContext ? 0
            : TypeSizes.UnboxedSize(type, pointerSize);

    /// <summary>
    /// Whether an access of <paramref name="accessSize"/> bytes at a member only <paramref name="memberSize"/>
    /// wide touches nothing but that member and its container's padding. ARM64 code clears or copies a
    /// trailing short together with its padding in one 8-byte access; padding holds no managed state, so
    /// the access is exactly one to the member. Every sibling needs a known extent, and the access must
    /// stay inside the container.
    /// </summary>
    private static bool OnlyPaddingFollows(List<GenericInstanceFieldLayout.FieldSlot>? siblings, long memberOffset,
        long memberSize, long accessSize, long containerSize)
    {
        var end = memberOffset + accessSize;
        return siblings != null && memberSize > 0 && containerSize > 0 && end <= containerSize
            && siblings.All(s => s.Size > 0
                && (s.Offset == memberOffset || s.Offset + s.Size <= memberOffset || s.Offset >= end));
    }

    internal static FieldReference? ResolvePartialStructAccess(FieldAnalysisContext field, LocalVariable receiver,
        int offset, int width, int pointerSize, IReadOnlyList<FieldAnalysisContext>? containingFields = null)
    {
        // A static field may be the outermost parent (Vector3.oneVector.x); FieldReference.IsStatic
        // then roots the access at the static storage instead of the receiver.
        if (width <= 0) return null;
        var parents = new List<FieldAnalysisContext>(containingFields ?? []);
        var seen = new HashSet<TypeAnalysisContext>();
        while (field.FieldType is { IsValueType: true } type && seen.Add(type) && StructFields(type) is { } fields)
        {
            if (fields.Where(f => f.Offset == 0).ToList() is not [{ } first]) return null;
            if (!ExtendsPastAccess(type, [])) return null;
            parents.Add(field);
            field = first.Field;
            if (ScalarSize(field.FieldType) == width)
                return new FieldReference(field, receiver, offset) { ContainingFields = parents.ToArray() };
        }
        return null;

        bool ExtendsPastAccess(TypeAnalysisContext type, HashSet<TypeAnalysisContext> visited)
        {
            if (!type.IsValueType || !visited.Add(type) || StructFields(type) is not { } fields) return false;
            return fields.Any(f => f.Offset >= width)
                || fields.Where(f => f.Offset == 0).ToList() is [{ } first] && ExtendsPastAccess(first.Field.FieldType, visited);
        }

        // A generic instance has no metadata offsets, so its members come from the computed layout,
        // bound to the instantiation. Explicit and packed layouts are not inferred.
        List<GenericInstanceFieldLayout.FieldSlot>? StructFields(TypeAnalysisContext type)
        {
            if (type is GenericInstanceTypeAnalysisContext)
                return GenericInstanceFieldLayout.ComputeLayout(type)?.Slots;
            if (type.GenericParameters.Count != 0
                || (type.Attributes & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout
                || type.Definition is { PackingSize: > 0 })
                return null;
            return type.Fields.Where(f => !f.IsStatic)
                .Select(f => new GenericInstanceFieldLayout.FieldSlot(f, f, f.Offset, 0)).ToList();
        }

        int ScalarSize(TypeAnalysisContext type) => type is GenericParameterTypeAnalysisContext ? 0
            : !type.IsValueType ? pointerSize : type.FullName switch
            {
                "System.Boolean" or "System.Byte" or "System.SByte" => 1,
                "System.Char" or "System.Int16" or "System.UInt16" => 2,
                "System.Int32" or "System.UInt32" or "System.Single" => 4,
                "System.Int64" or "System.UInt64" or "System.Double" => 8,
                "System.IntPtr" or "System.UIntPtr" => pointerSize,
                _ => 0
            };
    }

    private static bool IsByRefValueAggregateCopy(Instruction instruction, int memoryOperandIndex,
        MemoryOperand memory)
    {
        if (instruction.OpCode != OpCode.Move || instruction.Operands.Count != 2
            || memory.Addend != 0 || memory.Index != null || memory.Scale != 0
            || memory.Base is not LocalVariable { Type: ByRefTypeAnalysisContext { ElementType.IsValueType: true } })
            return false;

        var other = instruction.Operands[1 - memoryOperandIndex];
        return other is LocalVariable { Register.Name: ['X', ..] };
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

    // A register merged from several addresses (a branch or CSEL choosing &a.x, &b.y or a class's static
    // storage) takes its type from whichever input propagation reached first, so resolving a load through
    // it would read that input's member on every path. Resolve it only when every input addresses the same
    // member. Merged object references are fine: the load reads the member of whichever object arrives.
    internal static bool MergedBaseAgrees(LocalVariable local, long offset, Dictionary<LocalVariable, Instruction> definitions)
    {
        var inputs = new List<IOperand>();
        var visited = new HashSet<LocalVariable>();
        var pending = new Stack<IOperand>([local]);
        var merged = false;
        while (pending.TryPop(out var value))
        {
            if (value is LocalVariable variable && definitions.TryGetValue(variable, out var definition)
                && definition is { OpCode: OpCode.Phi } or { OpCode: OpCode.Move, Operands: [_, LocalVariable] })
            {
                if (!visited.Add(variable)) continue;
                merged |= definition.OpCode == OpCode.Phi;
                foreach (var source in definition.Operands.Skip(1)) pending.Push(source);
                continue;
            }
            inputs.Add(value);
        }
        if (!merged) return true;

        static bool IsAddress(TypeAnalysisContext? type) => type is StaticFieldStorageTypeAnalysisContext or ByRefTypeAnalysisContext;
        static TypeAnalysisContext? Owner(TypeAnalysisContext? type) => type switch
        {
            StaticFieldStorageTypeAnalysisContext storage => storage.OwnerType,
            ByRefTypeAnalysisContext byRef => byRef.ElementType,
            _ => type,
        };

        var expected = (Owner(local.Type), offset);
        var addressed = IsAddress(local.Type);
        var objects = false;
        object? address = null;
        foreach (var input in inputs)
        {
            if (input is Immediate { Value: 0 }) continue;
            // A constant or a frame address is an address, never an object reference.
            if (input is Immediate or AddressOf) return false;
            if (input is not LocalVariable inputLocal)
            {
                if (addressed) return false;
                objects = true;
                continue;
            }
            var baseLocal = inputLocal;
            var inputOffset = offset;
            UnwrapAddressUpdate(ref baseLocal, ref inputOffset, definitions);
            if (baseLocal == inputLocal && !IsAddress(inputLocal.Type))
            {
                objects = true;
                continue;
            }
            addressed = true;
            if (baseLocal.Type == null || !Equals(Owner(baseLocal.Type), expected.Item1) || inputOffset != expected.offset
                || IsAddress(baseLocal.Type) != IsAddress(local.Type))
                return false;
            // Equal types are not the same address: separate literal slots, or two objects' interiors.
            var identity = Identity(baseLocal, definitions);
            if (address == null) address = identity;
            else if (!Equals(address, identity)) return false;
        }
        return !(addressed && objects);
    }

    // What an address register holds: a class's static storage is the same wherever it is loaded;
    // any other value is only known to be itself.
    private static object Identity(LocalVariable local, Dictionary<LocalVariable, Instruction> definitions)
    {
        var visited = new HashSet<LocalVariable>();
        while (visited.Add(local) && definitions.TryGetValue(local, out var definition))
        {
            if (definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable copy] })
            {
                local = copy;
                continue;
            }
            if (definition is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: LocalVariable { Type: RuntimeClassTypeAnalysisContext klass }, Index: null } memory] })
                return (klass.RepresentedType, memory.Addend);
            break;
        }
        return local;
    }

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
                // A codegen thunk that only branches to a key function is handled as that function.
                target = keyFunctionAddresses.ResolveKeyFunctionAddress(target);
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

            if (MatchStaticByArgumentType(instruction, candidates) is { } byArgument)
            {
                instruction.SetOperand(0, byArgument);
                byArgument.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, byArgument);
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

            // Inside a generic type's own code 'this' is G<T1..Tn> over G's own parameters: the callee is G's
            // definition method, whose shared body the instantiations of G also register.
            if (receiverType is GenericInstanceTypeAnalysisContext selfInstance
                && IsOwnInstantiation(selfInstance, selfInstance.GenericType)
                && candidates.Where(c => !c.IsStatic && ReferenceEquals(c.DeclaringType, selfInstance.GenericType)).ToList() is [{ } own])
            {
                instruction.SetOperand(0, own);
                own.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, own);
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

    // Static methods of a generic type's instantiations share one body when the type arguments share a
    // representation, so there is no receiver to tell them apart. An argument declared as the type
    // itself (e.g. ScriptPlayable<T>.op_Implicit(ScriptPlayable<T>)) carries the instantiation.
    private static MethodAnalysisContext? MatchStaticByArgumentType(Instruction call, List<MethodAnalysisContext> candidates)
    {
        var definition = BaseMethodOf(candidates[0]);
        if (definition.DeclaringType is not { GenericParameters.Count: > 0 } genericType
            || definition.GenericParameters.Count != 0
            || candidates.Any(c => !c.IsStatic || !ReferenceEquals(BaseMethodOf(c), definition)))
            return null;

        var firstArg = call.OpCode == OpCode.CallVoid ? 1 : 2;
        for (var i = 0; i < definition.Parameters.Count && firstArg + i < call.Operands.Count; i++)
        {
            if (!IsOwnInstantiation(definition.Parameters[i].ParameterType, genericType)
                || call.Operands[firstArg + i] is not LocalVariable { Type: GenericInstanceTypeAnalysisContext argument }
                || !ReferenceEquals(argument.GenericType, genericType)
                || argument.GenericArguments.Any(a => a is GenericParameterTypeAnalysisContext))
                continue;

            return candidates.FirstOrDefault(c => IsSameType(c.DeclaringType, argument))
                   ?? new ConcreteGenericMethodAnalysisContext(definition, argument.GenericArguments, []);
        }

        return null;
    }

    // Whether type is genericType<T1..Tn> instantiated with its own type parameters, in order.
    private static bool IsOwnInstantiation(TypeAnalysisContext type, TypeAnalysisContext genericType)
        => type is GenericInstanceTypeAnalysisContext instance
           && ReferenceEquals(instance.GenericType, genericType)
           && instance.GenericArguments.Count == genericType.GenericParameters.Count
           && instance.GenericArguments.Select((a, i) => a is GenericParameterTypeAnalysisContext { Index: var index } && index == i).All(same => same);

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
                // The class operand is the exact runtime class allocated. The result's own type can be a
                // weaker static type propagated from a use before the class operand resolved.
                case OpCode.Newobj:
                    return definition.Operands[1] switch
                    {
                        RuntimeClassTypeAnalysisContext { RepresentedType: var allocated } => allocated,
                        LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: var allocated } } => allocated,
                        TypeAnalysisContext allocated => allocated,
                        _ => null,
                    } ?? (definition.Operands[0] as LocalVariable)?.Type;
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

            if (GetMethodInfoArgument(instruction, method) is not { RepresentedMethod: { } representedMethod })
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
                // having a normal method candidate (for example an adjustor/thunk-only entry), and a
                // generic instantiation the metadata never registered still has a real managed body.
                // Restrict this fallback to addresses explicitly listed as concrete generic
                // implementations, or to unregistered bodies of the generic method in the MethodInfo;
                // arbitrary native/runtime calls may reuse an X1 value that looks like a MethodInfo*
                // after register allocation.
                var registered = method.AppContext.Binary.ConcreteGenericImplementationsByAddress.ContainsKey(target.UnsignedValue);
                if (!registered && !MayBeUnregisteredGenericBody(method.AppContext, target.UnsignedValue, representedMethod))
                    continue;

                // Il2CPP still passes the concrete MethodInfo as the hidden final parameter, so use
                // a methodof there when available. Do not turn the caller's own MethodInfo into a
                // recursive target.
                if (ReferenceEquals(representedMethod, method))
                    continue;

                var firstArg = instruction.OpCode == OpCode.CallVoid ? 1 : 2;
                var hiddenParamIndex = firstArg
                    + (representedMethod.AppContext.InstructionSet.CallingConventionResolver?.ReturnBufferTakesArgumentSlot(representedMethod) == true ? 1 : 0)
                    + (representedMethod.IsStatic ? 0 : 1) + representedMethod.Parameters.Count;

                // Nothing but the MethodInfo identifies an unregistered body, so it must be the one
                // in the hidden parameter slot of the method it represents, and set for this call.
                if (hiddenParamIndex >= instruction.Operands.Count
                    || AsMethodInfo(instruction.Operands[hiddenParamIndex]) is not { } hiddenMethodInfo
                    || !registered && (!ReferenceEquals(hiddenMethodInfo.RepresentedMethod, representedMethod)
                        || !SetsArgumentRegisterAfterLastCall(method, instruction, hiddenParamIndex - firstArg)))
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

    // A call target outside MethodsByAddress may still be the shared or value-type body of a generic
    // method: those bodies serve several instantiations, so metadata need not list the address. Accept
    // only managed code that no runtime helper, export or import stub accounts for, and leave the
    // address out of MethodsByAddress; the caller's MethodInfo, not the address, identifies the method.
    private static bool MayBeUnregisteredGenericBody(ApplicationAnalysisContext app, ulong target, MethodAnalysisContext represented)
    {
        if (target < app.ManagedCodeStart || target > app.ManagedCodeEnd)
            return false;

        if (represented is not ConcreteGenericMethodAnalysisContext { MethodGenericParameters.Count: > 0 }
            && represented.DeclaringType is not GenericInstanceTypeAnalysisContext { GenericArguments.Count: > 0 })
            return false;

        return !app.GetOrCreateKeyFunctionAddresses().IsKeyFunctionAddress(target)
               && !app.Binary.IsExportedFunction(target)
               && !Arm64ImportResolver.IsImportStub(app.Binary, target);
    }

    // Lifting keeps argument registers live across calls, so the MethodInfo* loaded for an earlier call
    // can still occupy this call's hidden parameter register, even when this callee takes no MethodInfo
    // at all. Require the native code to set that register after the last call before this one, within
    // the call's block. Only ARM64 is checked; elsewhere nothing is proven.
    private static bool SetsArgumentRegisterAfterLastCall(MethodAnalysisContext method, Instruction call, int integerArgument)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet || integerArgument is < 0 or > 7
            || call.NativeAddress == 0 || method.ControlFlowGraph!.Blocks.FirstOrDefault(b => b.Instructions.Contains(call)) is not { } block)
            return false;

        var start = Math.Max(method.UnderlyingPointer,
            block.Instructions.Where(i => i.NativeAddress != 0).Min(i => i.NativeAddress));
        var bytes = method.RawBytes.AsSpan();
        var wide = Arm64Register.X0 + integerArgument;
        var narrow = Arm64Register.W0 + integerArgument;

        try
        {
            for (var pc = call.NativeAddress; pc >= start + 4;)
            {
                pc -= 4;
                var offset = pc - method.UnderlyingPointer;
                if (offset + 4 > (ulong)bytes.Length)
                    return false;

                if (Disassembler.Disassemble(bytes.Slice((int)offset, 4), pc, new Disassembler.Options(true, true, false)).ToList() is not [var previous])
                    return false;

                switch (previous.Mnemonic)
                {
                    case Arm64Mnemonic.BL or Arm64Mnemonic.BLR or Arm64Mnemonic.BR
                        or Arm64Mnemonic.RET or Arm64Mnemonic.RETAA or Arm64Mnemonic.RETAB or Arm64Mnemonic.INVALID:
                    case Arm64Mnemonic.B when previous.MnemonicConditionCode is Arm64ConditionCode.NONE or Arm64ConditionCode.AL:
                        return false;
                    case Arm64Mnemonic.LDR or Arm64Mnemonic.LDUR or Arm64Mnemonic.MOV or Arm64Mnemonic.ADD
                        or Arm64Mnemonic.ADRP or Arm64Mnemonic.ORR when previous.Op0Reg == wide || previous.Op0Reg == narrow:
                    case Arm64Mnemonic.LDP when previous.Op0Reg == wide || previous.Op1Reg == wide:
                        return true;
                }
            }
        }
        catch (Exception)
        {
            return false; // undecodable code proves nothing
        }

        return false;
    }

    private static bool CanSpecializeSharedGeneric(MethodAnalysisContext current, MethodAnalysisContext represented)
    {
        // Method arguments share a body too (object for reference types, the corlib enum of the same
        // underlying type for enums), even when their declaring type is not generic
        // (e.g. Enumerable.FirstOrDefault<T>).
        if (current is ConcreteGenericMethodAnalysisContext currentGeneric
            && represented is ConcreteGenericMethodAnalysisContext representedGeneric
            && ReferenceEquals(currentGeneric.BaseMethodContext, representedGeneric.BaseMethodContext)
            && IsSameType(current.DeclaringType, represented.DeclaringType)
            && currentGeneric.MethodGenericParameters.Count > 0
            && currentGeneric.MethodGenericParameters.Count == representedGeneric.MethodGenericParameters.Count)
        {
            var changed = false;
            for (var i = 0; i < currentGeneric.MethodGenericParameters.Count; i++)
            {
                var before = currentGeneric.MethodGenericParameters[i];
                var after = representedGeneric.MethodGenericParameters[i];
                if (IsSameType(before, after)) continue;
                if (!GenericSharing.IsSharedFormOf(before, after))
                    return false; // Not a refinement of the shared body.
                changed = true;
            }
            return changed;
        }

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

        // IL2CPP compiles System.Object bodies for reference-type arguments and corlib enum bodies for enums.
        return instance.GenericArguments.Any(GenericSharing.IsSharedRepresentative);
    }

    private static bool MatchesSharedGenericMethod(MethodAnalysisContext shared, MethodAnalysisContext represented)
    {
        if (!IsSharedGenericMethod(shared)
            || shared.Name != represented.Name
            || shared.IsStatic != represented.IsStatic
            || shared.Parameters.Count != represented.Parameters.Count)
            return false;

        if (ReferenceEquals(BaseMethodOf(shared), BaseMethodOf(represented)))
            return GenericSharing.MayServe(shared, represented);

        return shared.DeclaringType is GenericInstanceTypeAnalysisContext sharedInstance
            && represented.DeclaringType is GenericInstanceTypeAnalysisContext representedInstance
            && ReferenceEquals(sharedInstance.GenericType, representedInstance.GenericType)
            && sharedInstance.GenericArguments.Count == representedInstance.GenericArguments.Count
            && GenericSharing.MayServe(sharedInstance.GenericArguments, representedInstance.GenericArguments);
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

            // A receiver the shared body cannot serve contradicts the call target.
            if (!GenericSharing.MayServe(sharedInstance.GenericArguments, receiverInstance.GenericArguments))
                return null;

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
                if ((ResolveVTableSlot(method.AppContext, receiverType, slot)
                     ?? ResolveVTableSlotOfProvenReceiver(method, klassLocal, receiverType, slot, loads)) is not { } resolved)
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

        // A MethodInfo* read out of a vtable slot on its own is the method a delegate to a virtual method
        // binds to (ldvirtftn): IL2CPP builds new Action(this.M) from the VirtualInvokeData's method.
        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (instruction is not { OpCode: OpCode.Move, Operands: [LocalVariable destination, MemoryOperand
                {
                    Base: LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: { } ownerType } },
                    Index: null, Scale: 0, Addend: var addend
                }] })
                continue;

            var offset = addend - vtableOffset - pointerSize;
            if (offset < 0 || offset % invokeDataSize != 0
                || ResolveVTableSlot(method.AppContext, ownerType, (int)(offset / invokeDataSize)) is not { } slotMethod
                || (slotMethod.DeclaringType?.DeclaringAssembly ?? method.DeclaringType?.DeclaringAssembly) is not { } slotAssembly)
                continue;

            var methodInfo = new RuntimeMethodInfoAnalysisContext(slotMethod, slotAssembly);
            instruction.SetOperand(1, methodInfo);
            destination.Type = methodInfo;
            changed = true;
        }

        return changed;

        MemoryOperand? SlotLoad(IOperand operand) => operand switch
        {
            MemoryOperand { Index: null, Scale: 0 } inlined => inlined,
            LocalVariable local when loads.TryGetValue(local, out var load) => load,
            _ => null
        };
    }

    // The klass was read from an object typed only as a base class (e.g. Object from a shared generic
    // InstantiateDialog<T>), whose vtable has no such slot. A call to an instance method of a derived type
    // D with that object as the receiver proves it is a D, so the slot is looked up in D's vtable instead.
    private static MethodAnalysisContext? ResolveVTableSlotOfProvenReceiver(MethodAnalysisContext method, LocalVariable klassLocal,
        TypeAnalysisContext receiverType, int slot, Dictionary<LocalVariable, MemoryOperand> loads)
    {
        if (!loads.TryGetValue(klassLocal, out var klassLoad)
            || klassLoad is not { Base: LocalVariable instance, Addend: 0 })
            return null;

        var aliases = new HashSet<LocalVariable> { instance };
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
            if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable copy, LocalVariable source] } && aliases.Contains(source))
                aliases.Add(copy);

        bool Derives(TypeAnalysisContext? type)
        {
            for (var baseType = type?.BaseType; baseType != null; baseType = baseType.BaseType)
                if (baseType.FullName == receiverType.FullName)
                    return true;
            return false;
        }

        var proven = method.ControlFlowGraph.Instructions
            .Where(i => i.IsCall && i.Operands[0] is MethodAnalysisContext { IsStatic: false }
                && i.Operands.Count > (i.OpCode == OpCode.CallVoid ? 1 : 2)
                && i.Operands[i.OpCode == OpCode.CallVoid ? 1 : 2] is LocalVariable receiver && aliases.Contains(receiver))
            .Select(i => ((MethodAnalysisContext)i.Operands[0]).DeclaringType)
            .Where(Derives).Distinct().ToList();

        // Or the object is what a generic method returns as its own type argument (T InstantiateDialog<T>()),
        // called from shared code whose only method type parameter is constrained to a class deriving from
        // the klass type: that argument is the caller's T, so the object is at least its constraint.
        if (proven.Count == 0
            && Producer(instance) is { OpCode: OpCode.Call, Operands: [MethodAnalysisContext producer, ..] }
            && BaseMethodOf(producer).ReturnType is GenericParameterTypeAnalysisContext { Type: Il2CppTypeEnum.IL2CPP_TYPE_MVAR }
            && method.GenericParameters is [{ } typeParameter]
            && typeParameter.ConstraintTypes.Where(c => !c.IsInterface && Derives(c)).ToList() is [{ } constraint])
            proven.Add(constraint);

        // The instruction that produced a value, looking through copies.
        Instruction? Producer(LocalVariable value)
        {
            var seen = new HashSet<LocalVariable>();
            while (seen.Add(value) && method.ControlFlowGraph.Instructions.FirstOrDefault(i => ReferenceEquals(i.Destination, value)) is { } definition)
            {
                if (definition is not { OpCode: OpCode.Move, Operands: [_, LocalVariable source] })
                    return definition;
                value = source;
            }
            return null;
        }

        // The most derived of them, provided they form one chain.
        var mostDerived = proven.FirstOrDefault(candidate => proven.All(other => other == candidate || IsSubclass(candidate, other)));
        return mostDerived == null ? null : ResolveVTableSlot(method.AppContext, mostDerived, slot);

        static bool IsSubclass(TypeAnalysisContext type, TypeAnalysisContext ancestor)
        {
            for (var baseType = type.BaseType; baseType != null; baseType = baseType.BaseType)
                if (baseType.FullName == ancestor.FullName)
                    return true;
            return false;
        }
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

    // The caller's own MethodInfo can linger in a later argument register after the call's real one
    // (a static callee taking only its MethodInfo in X0, with the caller's still in X1); skip it.
    private static RuntimeMethodInfoAnalysisContext? GetMethodInfoArgument(Instruction call, MethodAnalysisContext? caller = null)
    {
        var firstArg = call.OpCode == OpCode.CallVoid ? 1 : 2;

        for (var i = call.Operands.Count - 1; i >= firstArg; i--)
        {
            if (AsMethodInfo(call.Operands[i]) is { } methodInfo && !ReferenceEquals(methodInfo.RepresentedMethod, caller))
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
