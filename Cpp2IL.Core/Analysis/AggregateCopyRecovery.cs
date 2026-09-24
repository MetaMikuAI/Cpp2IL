using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

// Recover a native by-value parameter copy before field resolution mistakes wide
// loads for individual members. Requires SSA and a complete, isolated copy region.
public static class AggregateCopyRecovery
{
    private record Chunk(Instruction Load, Instruction Store, long Offset, int Size);

    public static bool Run(MethodAnalysisContext method)
    {
        var parameters = method.ParameterLocals.Where(p => !p.IsThis && p.Type is
            { IsValueType: true, IsEnumType: false, GenericParameters.Count: 0,
                Type: Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE, Definition: not null }).ToHashSet();
        var changed = RecoverReturnBufferCopy(method);
        changed |= RecoverRegisterCompositeCopies(method);
        if (parameters.Count == 0)
            return changed;
        var cfg = method.ControlFlowGraph!;
        var instructions = cfg.Instructions;
        var definitions = instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());
        var uses = instructions.SelectMany(DeadCodeEliminator.UsedLocals).GroupBy(l => l)
            .ToDictionary(g => g.Key, g => g.Count());
        foreach (var block in cfg.Blocks)
        {
            var copies = new Dictionary<(LocalVariable Source, LocalVariable Target, long Offset), List<Chunk>>();
            foreach (var store in block.Instructions)
            {
                if (store is not { OpCode: OpCode.Move, Operands: [MemoryOperand target, LocalVariable value] }
                    || target is not { Base: LocalVariable receiver, Index: null, Scale: 0, AccessSize: > 0 }
                    || !definitions.TryGetValue(value, out var load)
                    || load is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand source] }
                    || source is not { Base: LocalVariable parameter, Index: null, Scale: 0, Addend: >= 0 }
                    || source.AccessSize != target.AccessSize || uses.GetValueOrDefault(value) != 1
                    || !parameters.Contains(parameter)
                    || receiver.Type is not { IsValueType: false } || !block.Instructions.Contains(load)
                    || target.Addend < source.Addend)
                    continue;
                var key = (parameter, receiver, target.Addend - source.Addend);
                if (!copies.TryGetValue(key, out var chunks))
                    copies[key] = chunks = [];
                chunks.Add(new Chunk(load, store, source.Addend, source.AccessSize));
            }

            foreach (var (key, chunks) in copies)
            {
                var type = key.Source.Type!;
                var size = TypeSizes.UnboxedSize(type, method.AppContext.Binary.PointerSizeBytes);
                if (size <= 0 || key.Offset > int.MaxValue)
                    continue;
                var covered = 0L;
                foreach (var chunk in chunks.OrderBy(c => c.Offset))
                {
                    if (chunk.Offset != covered || chunk.Size > size - covered)
                        break;
                    covered += chunk.Size;
                }
                if (covered != size || chunks.Sum(c => (long)c.Size) != size
                    || FindField(key.Target.Type!, key.Offset) is not { } field || field.FieldType != type)
                    continue;

                var firstLoad = chunks.Min(c => block.Instructions.IndexOf(c.Load));
                var lastLoad = chunks.Max(c => block.Instructions.IndexOf(c.Load));
                var firstStore = chunks.Min(c => block.Instructions.IndexOf(c.Store));
                var lastStore = chunks.Max(c => block.Instructions.IndexOf(c.Store));
                var region = chunks.SelectMany(c => new[] { c.Load, c.Store }).ToHashSet();
                // All source bytes are captured before writing, and no other memory access,
                // call, branch, or address escape can observe/interfere with a partial copy.
                if (lastLoad >= firstStore || block.Instructions.Skip(firstLoad).Take(lastStore - firstLoad + 1)
                    .Any(i => i.OpCode != OpCode.Nop && !region.Contains(i)))
                    continue;
                foreach (var instruction in region)
                {
                    instruction.OpCode = OpCode.Nop;
                    instruction.SetOperands();
                }
                var assignment = block.Instructions[firstStore];
                assignment.OpCode = OpCode.Move;
                assignment.SetOperands(new FieldReference(field, key.Target, (int)key.Offset), key.Source);
                changed = true;
            }
        }
        return changed;
    }

    // A full field-to-return-buffer copy is one managed value assignment, not a
    // sequence of loads of the members starting at each native chunk offset.
    private static bool RecoverReturnBufferCopy(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet.CallingConventionResolver?.HiddenReturnBufferRegister(method) is not { } register
            || method.Locals.FirstOrDefault(l => l.Register.Number == register.Number && l.Register.Version == -1) is not { } buffer)
            return false;
        var size = TypeSizes.UnboxedSize(method.ReturnType, method.AppContext.Binary.PointerSizeBytes);
        if (size <= 0) return false;
        var instructions = method.ControlFlowGraph!.Instructions;
        var definitions = instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());
        var uses = instructions.SelectMany(DeadCodeEliminator.UsedLocals).GroupBy(l => l)
            .ToDictionary(g => g.Key, g => g.Count());
        var changed = false;
        foreach (var block in method.ControlFlowGraph.Blocks)
        {
            var copies = new Dictionary<(LocalVariable Owner, long Offset), List<Chunk>>();
            foreach (var store in block.Instructions)
            {
                if (store is not { OpCode: OpCode.Move, Operands: [MemoryOperand target, LocalVariable value] }
                    || target is not { Index: null, Scale: 0, Addend: >= 0, AccessSize: > 0 }
                    || target.Base != buffer || !definitions.TryGetValue(value, out var load)
                    || uses.GetValueOrDefault(value) != 1
                    || load is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand source] }
                    || source is not { Base: LocalVariable { Type: { IsValueType: false } } owner, Index: null, Scale: 0 }
                    || source.AccessSize != target.AccessSize || source.Addend < target.Addend
                    || !block.Instructions.Contains(load)) continue;
                var key = (owner, source.Addend - target.Addend);
                if (!copies.TryGetValue(key, out var chunks)) copies[key] = chunks = [];
                chunks.Add(new Chunk(load, store, target.Addend, target.AccessSize));
            }
            foreach (var (key, chunks) in copies)
            {
                if (key.Offset > int.MaxValue || FindField(key.Owner.Type!, key.Offset) is not { } field
                    || field.FieldType != method.ReturnType) continue;
                var covered = 0L;
                foreach (var chunk in chunks.OrderBy(c => c.Offset))
                {
                    if (chunk.Offset != covered || chunk.Size > size - covered) break;
                    covered += chunk.Size;
                }
                if (covered != size || chunks.Sum(c => (long)c.Size) != size) continue;
                var firstLoad = chunks.Min(c => block.Instructions.IndexOf(c.Load));
                var lastLoad = chunks.Max(c => block.Instructions.IndexOf(c.Load));
                var firstStore = chunks.Min(c => block.Instructions.IndexOf(c.Store));
                var lastStore = chunks.Max(c => block.Instructions.IndexOf(c.Store));
                var region = chunks.SelectMany(c => new[] { c.Load, c.Store }).ToHashSet();
                if (lastLoad >= firstStore || block.Instructions.Skip(firstLoad).Take(lastStore - firstLoad + 1)
                    .Any(i => i.OpCode != OpCode.Nop && !region.Contains(i))) continue;
                foreach (var instruction in region)
                {
                    instruction.OpCode = OpCode.Nop;
                    instruction.SetOperands();
                }
                var assignment = block.Instructions[firstStore];
                assignment.OpCode = OpCode.Move;
                assignment.SetOperands(buffer, new FieldReference(field, key.Owner, (int)key.Offset));
                changed = true;
            }
        }
        return changed;
    }

    // An ARM64 composite of 9-16 bytes travels in two X registers, one member each. The lifter
    // names the value's storage at the ABI boundary (composite_parameter_n, composite_ret_*,
    // composite_arg_*). Storing both registers of one value, unchanged, into a field or into such
    // storage is one assignment of the whole value.
    private static bool RecoverRegisterCompositeCopies(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        var definitions = cfg.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());
        var changed = false;
        foreach (var block in cfg.Blocks)
        {
            var list = block.Instructions;
            for (var low = 0; low < list.Count; low++)
            {
                if (list[low] is not { OpCode: OpCode.Move, Operands: [var lowTarget, LocalVariable lowValue] }
                    || Access(lowTarget) is not { } lowAccess)
                    continue;
                var (target, targetOffset, lowSize) = lowAccess;
                var high = low + 1;
                while (high < list.Count && list[high].OpCode == OpCode.Nop)
                    high++;
                if (high == list.Count || list[high] is not { OpCode: OpCode.Move, Operands: [var highTarget, LocalVariable highValue] }
                    || Access(highTarget) is not { } highAccess
                    || highAccess.Base != target || highAccess.Offset != targetOffset + 8)
                    continue;
                var highSize = highAccess.Size;

                // The destination: composite storage itself, or a field of that type in an object.
                FieldAnalysisContext? targetField = null;
                TypeAnalysisContext? type;
                if (IsCompositeStorage(target, out _))
                {
                    if (targetOffset != 0) continue;
                    type = target.Type;
                }
                else if (target.Type is { IsValueType: false } owner && FindField(owner, targetOffset) is { } field)
                    (targetField, type) = (field, field.FieldType);
                else continue;
                if (type == null || Arm64CallingConventionResolver.IntegerCompositeMembers(type) is not { } members
                    || !Covers(lowSize, members[0].Size) || !Covers(highSize, members[1].Size))
                    continue;

                if (Source(lowValue, 0, members[0].Size) is not { } lowHalf
                    || Source(highValue, 8, members[1].Size) is not { } highHalf
                    || highHalf.Base != lowHalf.Base || highHalf.Offset != lowHalf.Offset)
                    continue;
                var (source, sourceOffset, lowLoad) = lowHalf;
                var highLoad = highHalf.Load;

                IOperand value;
                if (IsCompositeStorage(source, out var immutable) && immutable && sourceOffset == 0 && source.Type == type)
                    value = source;
                else if (source.Type is { IsValueType: false } sourceOwner && FindField(sourceOwner, sourceOffset) is { } sourceField
                         && sourceField.FieldType == type && lowLoad != null && highLoad != null
                         && Unobserved(list, lowLoad, highLoad, high, target))
                    value = new FieldReference(sourceField, source, (int)sourceOffset);
                else continue;

                list[low].SetOperands(targetField == null ? target : new FieldReference(targetField, target, (int)targetOffset), value);
                list[high].OpCode = OpCode.Nop;
                list[high].SetOperands();
                changed = true;
            }
        }
        return changed;

        // The half of a value that local holds: a load at member offset half of [base + offset].
        (LocalVariable Base, long Offset, Instruction? Load)? Source(LocalVariable local, long half, int memberSize)
        {
            for (var depth = 0; depth < 4 && definitions.TryGetValue(local, out var definition); depth++)
            {
                if (definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable copied] })
                {
                    local = copied;
                    continue;
                }
                if (definition is not { OpCode: OpCode.Move, Operands: [_, var loaded] }
                    || Access(loaded) is not { } load || !Covers(load.Size, memberSize) || load.Offset < half)
                    return null;
                return (load.Base, load.Offset - half, definition);
            }
            return null;
        }

        // Nothing between the loads and the last store may write memory the loads read.
        bool Unobserved(List<Instruction> list, Instruction lowLoad, Instruction highLoad, int lastStore, LocalVariable target)
        {
            var first = System.Math.Min(list.IndexOf(lowLoad), list.IndexOf(highLoad));
            if (first < 0 || first > lastStore)
                return false;
            for (var i = first; i < lastStore; i++)
            {
                var instruction = list[i];
                if (instruction.IsCall || instruction.OpCode is OpCode.IndirectCall or OpCode.Invalid or OpCode.NotImplemented)
                    return false;
                if (instruction.Destination is MemoryOperand or FieldReference
                    && !(Access(instruction.Destination) is { } written
                         && (written.Base == target || IsCompositeStorage(written.Base, out _))))
                    return false;
            }
            return true;
        }
    }

    // Register-held composite storage; immutable when nothing but the ABI boundary writes it.
    private static bool IsCompositeStorage(LocalVariable local, out bool immutable)
    {
        var name = local.Register.Name ?? "";
        immutable = name.StartsWith("composite_parameter_") || name.StartsWith("composite_ret_");
        return immutable || name.StartsWith("composite_arg_");
    }

    // A register store or load of 8 bytes, or of the member's own size, carries the whole member.
    private static bool Covers(int accessSize, int memberSize) => accessSize == memberSize || accessSize == 8;

    private static (LocalVariable Base, long Offset, int Size)? Access(IOperand operand) => operand switch
    {
        MemoryOperand { Base: LocalVariable local, Index: null, Scale: 0, AccessSize: > 0 } memory
            => (local, memory.Addend, memory.AccessSize),
        FieldReference { IsStatic: false } field => (field.Local, field.Offset, FieldSize(field.Field)),
        _ => null
    };

    private static int FieldSize(FieldAnalysisContext field) => !field.FieldType.IsValueType ? 8
        : (int)TypeSizes.UnboxedSize(field.FieldType, field.AppContext.Binary.PointerSizeBytes);

    private static FieldAnalysisContext? FindField(TypeAnalysisContext owner, long offset)
    {
        for (var current = owner; current != null; current = current.BaseType)
        {
            if (current is GenericInstanceTypeAnalysisContext generic)
            {
                if (GenericInstanceFieldLayout.FindFieldAtOffset(generic, offset) is { } field)
                    return new ConcreteGenericFieldAnalysisContext(field, generic);
            }
            else if (current.GenericParameters.Count == 0)
            {
                if (current.Fields.FirstOrDefault(f => !f.IsStatic && f.BackingData?.FieldOffset == offset) is { } field)
                    return field;
            }
        }
        return null;
    }
}
