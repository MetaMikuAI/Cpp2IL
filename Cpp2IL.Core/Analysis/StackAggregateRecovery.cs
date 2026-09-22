using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

// Address-taken aggregates are storage, not independent SSA values for each native store.
internal static class StackAggregateRecovery
{
    private sealed record Member(long Offset, long Size, FieldAnalysisContext[] Path);
    private sealed record Storage(int Offset, long Size, TypeAnalysisContext Type, List<Member> Members);

    internal static void Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet) return;
        var roots = new HashSet<(int Offset, TypeAnalysisContext Type)>();
        var zeros = new HashSet<Instruction>();
        var addressOrs = new HashSet<Instruction>();
        foreach (var block in method.ControlFlowGraph!.Blocks)
        {
            var addresses = new Dictionary<int, int>();
            var zeroRegisters = new HashSet<int>();
            foreach (var instruction in block.Instructions)
            {
                if (instruction is { OpCode: OpCode.CallVoid, Operands: [var target, Register receiver, ..] }
                    && addresses.TryGetValue(receiver.Number, out var offset))
                {
                    var called = target as MethodAnalysisContext;
                    if (target is Immediate immediate && method.AppContext.MethodsByAddress.TryGetValue(immediate.UnsignedValue, out var candidates)
                        && candidates is [{ } unique]) called = unique;
                    // A shared List<object>.Enumerator body is not evidence that the caller's
                    // storage is object-instantiated. Wait for generic call specialization instead.
                    if (called is { IsStatic: false, DeclaringType: { IsValueType: true } type }
                        && type is not GenericInstanceTypeAnalysisContext && type.GenericParameters.Count == 0)
                        roots.Add((offset, type));
                }
                int? address = instruction switch
                {
                    { OpCode: OpCode.Move, Operands: [Register, AddressOf { Target: StackOffset slot }] } => slot.Offset,
                    { OpCode: OpCode.Move, Operands: [Register, Register copiedSource] } when addresses.TryGetValue(copiedSource.Number, out var copied) => copied,
                    _ => null
                };
                if (instruction is { OpCode: OpCode.Or, Operands: [_, Register source, Immediate { Value: >= 0 and < 16 } mask] }
                    && addresses.TryGetValue(source.Number, out var baseOffset) && (baseOffset & mask.Value) == 0)
                    addressOrs.Add(instruction); // ARM64 SP is 16-byte aligned; these bits are proven zero.
                var zero = instruction is { OpCode: OpCode.Move, Operands: [_, var value] }
                    && (value is Immediate { Value: 0 } || value is Register register && zeroRegisters.Contains(register.Number));
                if (zero) zeros.Add(instruction);
                if (instruction.Destination is Register destination)
                {
                    addresses.Remove(destination.Number);
                    zeroRegisters.Remove(destination.Number);
                    if (address.HasValue) addresses[destination.Number] = address.Value;
                    if (zero) zeroRegisters.Add(destination.Number);
                }
                if (instruction.IsCall) { addresses.Clear(); zeroRegisters.Clear(); }
            }
        }
        Recover(method, roots, zeros);
        foreach (var instruction in addressOrs)
            if (method.StackAggregates.Count != 0) instruction.OpCode = OpCode.Add;
    }

    internal static void Recover(MethodAnalysisContext method, IEnumerable<(int Offset, TypeAnalysisContext Type)> roots,
        HashSet<Instruction> zeros)
    {
        var storages = new List<Storage>();
        foreach (var (offset, type) in roots)
        {
            var size = TypeSizes.UnboxedSize(type, method.AppContext.Binary.PointerSizeBytes);
            var members = Layout(type, 0, [], []);
            if (size > 16 && members is { Count: > 0 } && members.All(m => m.Offset >= 0 && m.Offset + m.Size <= size))
                storages.Add(new(offset, size, type, members));
        }
        foreach (var storage in storages)
        {
            if (storages.Any(other => !ReferenceEquals(other, storage) && other.Offset < storage.Offset + storage.Size
                && storage.Offset < other.Offset + other.Size)) continue;
            var instructions = method.ControlFlowGraph!.Instructions;
            bool Within(StackOffset slot) => slot.Offset >= storage.Offset && slot.Offset < storage.Offset + storage.Size;
            bool Overlaps(StackOffset slot) => slot.Offset < storage.Offset + storage.Size
                && slot.Offset + Math.Max(slot.AccessSize, 1) > storage.Offset;
            var accesses = instructions.Where(i => i.Operands.Any(o => o is StackOffset slot && Overlaps(slot))).ToList();
            if (accesses.Any(i => i.OpCode != OpCode.Move || i.Operands.Count != 2
                || i.Operands.OfType<StackOffset>().Any(slot => !Within(slot) || slot.AccessSize <= 0
                    || slot.Offset + slot.AccessSize > storage.Offset + storage.Size
                    || !(zeros.Contains(i) && i.Operands[0] is StackOffset
                        ? storage.Members.Where(m => m.Offset < slot.Offset - storage.Offset + slot.AccessSize && m.Offset + m.Size > slot.Offset - storage.Offset)
                            .All(m => m.Offset >= slot.Offset - storage.Offset && m.Offset + m.Size <= slot.Offset - storage.Offset + slot.AccessSize)
                        : Find(storage.Type, slot.Offset - storage.Offset, slot.AccessSize, false) != null)))) continue;
            if (instructions.Any(i => i.Operands.Any(o => o is AddressOf { Target: StackOffset slot } && Within(slot)
                && slot.Offset != storage.Offset && i is not { OpCode: OpCode.Move, Operands: [Register, AddressOf] }))) continue;

            var owner = new Register(null, $"aggregate_stack_{storage.Offset}");
            method.StackAggregates.Add(owner.Number, storage.Type);
            foreach (var block in method.ControlFlowGraph.Blocks)
            {
                foreach (var instruction in block.Instructions.ToList())
                {
                    if (zeros.Contains(instruction) && instruction.Operands is [StackOffset zeroSlot, _] && Within(zeroSlot))
                    {
                        var leaves = storage.Members.Where(m => m.Offset >= zeroSlot.Offset - storage.Offset
                            && m.Offset + m.Size <= zeroSlot.Offset - storage.Offset + zeroSlot.AccessSize).ToList();
                        var position = block.Instructions.IndexOf(instruction);
                        instruction.OpCode = OpCode.Nop;
                        instruction.SetOperands();
                        foreach (var member in leaves)
                            block.Instructions.Insert(position++, new Instruction(-1, OpCode.Move,
                                new MemoryOperand(owner, addend: member.Offset, accessSize: (int)member.Size), new Immediate(0)));
                        continue;
                    }
                    for (var i = 0; i < instruction.Operands.Count; i++)
                    {
                        if (instruction.Operands[i] is StackOffset slot && Within(slot))
                            instruction.SetOperand(i, new MemoryOperand(owner, addend: slot.Offset - storage.Offset, accessSize: slot.AccessSize));
                        else if (instruction.Operands[i] is AddressOf { Target: StackOffset addressed } && Within(addressed))
                        {
                            if (addressed.Offset == storage.Offset) instruction.SetOperand(i, new AddressOf(owner));
                            else
                            {
                                instruction.OpCode = OpCode.Add;
                                instruction.SetOperands(instruction.Operands[0], new AddressOf(owner), new Immediate(addressed.Offset - storage.Offset));
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    internal static void ResolveFields(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
            for (var i = 0; i < instruction.Operands.Count; i++)
                if (instruction.Operands[i] is MemoryOperand { Base: LocalVariable owner, Index: null, Scale: 0 } memory
                    && method.StackAggregates.TryGetValue(owner.Register.Number, out var type)
                    && Find(type, memory.Addend, memory.AccessSize, i == 0 && instruction.Operands[1] is Immediate { Value: 0 }) is { } member)
                    instruction.SetOperand(i, new FieldReference(member.Path[^1], owner, (int)memory.Addend)
                        { ContainingFields = member.Path[..^1] });
    }

    private static Member? Find(TypeAnalysisContext type, long offset, int size, bool leafOnly)
    {
        foreach (var (field, fieldOffset, fieldSize) in Fields(type) ?? [])
        {
            if (offset < fieldOffset || offset + size > fieldOffset + fieldSize) continue;
            if (offset == fieldOffset && size == fieldSize && (!leafOnly || !Aggregate(field.FieldType)))
                return new(offset, size, [field]);
            if (Aggregate(field.FieldType) && Find(field.FieldType, offset - fieldOffset, size, leafOnly) is { } nested)
                return new(offset, size, [field, .. nested.Path]);
        }
        return null;
    }

    private static List<Member>? Layout(TypeAnalysisContext type, long offset, FieldAnalysisContext[] parents, HashSet<TypeAnalysisContext> seen)
    {
        if (!seen.Add(type) || Fields(type) is not { } fields) return null;
        var result = new List<Member>();
        foreach (var (field, fieldOffset, size) in fields)
        {
            if (fieldOffset < 0 || size <= 0) return null;
            if (Aggregate(field.FieldType))
            {
                var nested = Layout(field.FieldType, offset + fieldOffset, [.. parents, field], new(seen));
                if (nested == null) return null;
                result.AddRange(nested);
            }
            else result.Add(new(offset + fieldOffset, size, [.. parents, field]));
        }
        var ordered = result.OrderBy(m => m.Offset).ToList();
        if (ordered.Zip(ordered.Skip(1)).Any(p => p.First.Offset + p.First.Size > p.Second.Offset)) return null;
        return ordered;
    }

    private static List<(FieldAnalysisContext Field, long Offset, long Size)>? Fields(TypeAnalysisContext type)
    {
        var instance = type as GenericInstanceTypeAnalysisContext;
        var definition = instance?.GenericType ?? type;
        if ((definition.Attributes & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout
            || definition.Definition is { PackingSize: > 0 } || instance == null && type.GenericParameters.Count != 0
            || instance != null && instance.GenericArguments.Any(t => t.IsValueType || t is GenericParameterTypeAnalysisContext)) return null;
        var fields = new List<(FieldAnalysisContext, long, long)>();
        long offset = 0;
        foreach (var original in definition.Fields.Where(f => !f.IsStatic))
        {
            FieldAnalysisContext field = instance == null ? original : new ConcreteGenericFieldAnalysisContext(original, instance);
            var size = Size(field.FieldType);
            if (size <= 0) return null;
            if (instance != null)
            {
                // This bounded layout supports reference instantiations with scalar fields or
                // nested reference instantiations; arbitrary inline structs need their own ABI alignment.
                if (Aggregate(field.FieldType) && field.FieldType is not GenericInstanceTypeAnalysisContext) return null;
                var alignment = Math.Min(size, type.AppContext.Binary.PointerSizeBytes);
                if ((alignment & (alignment - 1)) != 0) return null;
                offset = (offset + alignment - 1) & ~(alignment - 1);
            }
            else offset = field.Offset;
            fields.Add((field, offset, size));
            offset += size;
        }
        return fields;
    }

    private static bool Aggregate(TypeAnalysisContext type) => type.IsValueType && !type.IsEnumType
        && type.Type is Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE or Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST;
    private static long Size(TypeAnalysisContext type) => type.IsValueType
        ? TypeSizes.UnboxedSize(type, type.AppContext.Binary.PointerSizeBytes) : type.AppContext.Binary.PointerSizeBytes;
}
