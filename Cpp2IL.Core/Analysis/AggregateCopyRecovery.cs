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
        if (parameters.Count == 0)
            return false;
        var cfg = method.ControlFlowGraph!;
        var instructions = cfg.Instructions;
        var definitions = instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());
        var uses = instructions.SelectMany(DeadCodeEliminator.UsedLocals).GroupBy(l => l)
            .ToDictionary(g => g.Key, g => g.Count());
        var changed = false;
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
