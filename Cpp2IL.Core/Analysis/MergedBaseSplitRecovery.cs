using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A switch picking one of several static fields by address (ColorUtility's colour constants: each arm sets
/// storage + its field's offset) merges the addresses in a phi, and the read through it can then come from
/// any of the fields, which field resolution rightly refuses. Read each field on its own path instead: every
/// predecessor loads from its own address, and the read becomes a phi of those values, each a plain static
/// field read. Only reads before any store or call in the merge block are moved, so none can see a
/// different value on the path it now runs on.
/// </summary>
public static class MergedBaseSplitRecovery
{
    public static bool Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var definitions = graph.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());

        var changed = false;
        foreach (var block in graph.Blocks.ToList())
        {
            var predecessors = block.Predecessors.ToList();
            if (predecessors.Count < 2 || predecessors.Distinct().Count() != predecessors.Count)
                continue;

            // Merged addresses: a phi whose every input is a typed base plus a constant (or the base itself):
            // one class's static storage, loaded on each path, or objects' fields. Reading on each path is the
            // same read the merged address makes; a null input is left alone rather than dereferenced.
            var merged = new Dictionary<LocalVariable, (LocalVariable[] Storages, long[] Offsets)>();
            foreach (var phi in block.Instructions.TakeWhile(i => i.OpCode is OpCode.Phi or OpCode.Nop).Where(i => i.OpCode == OpCode.Phi))
            {
                if (phi.Operands[0] is not LocalVariable address || phi.Operands.Count - 1 != predecessors.Count)
                    continue;
                var storages = new LocalVariable[predecessors.Count];
                var offsets = new long[predecessors.Count];
                var usable = true;
                for (var i = 0; i < offsets.Length; i++)
                {
                    if (phi.Operands[i + 1] is not LocalVariable input)
                    {
                        usable = false;
                        break;
                    }
                    if (definitions.TryGetValue(input, out var definition)
                        && definition is { OpCode: OpCode.Add, Operands: [_, LocalVariable { Type: { } baseType } baseLocal, Immediate offset] }
                        && IsBase(baseType))
                    {
                        storages[i] = baseLocal;
                        offsets[i] = offset.Value;
                    }
                    else if (input.Type is StaticFieldStorageTypeAnalysisContext)
                    {
                        storages[i] = input;
                        offsets[i] = 0;
                    }
                    else
                    {
                        usable = false;
                        break;
                    }
                }
                // Only a genuine merge of different addresses; one address throughout resolves already.
                if (usable && storages.Select((b, i) => (b, offsets[i])).Distinct().Count() > 1)
                    merged[address] = (storages, offsets);
            }
            if (merged.Count == 0)
                continue;

            var phiEnd = block.Instructions.FindLastIndex(i => i.OpCode == OpCode.Phi) + 1;
            for (var index = phiEnd; index < block.Instructions.Count; index++)
            {
                var instruction = block.Instructions[index];
                if (instruction.IsCall || instruction.OpCode is OpCode.IndirectCall or OpCode.IndirectJump || instruction.Destination is MemoryOperand or FieldReference)
                    break;
                if (instruction is not { OpCode: OpCode.Move, Operands: [LocalVariable loaded, MemoryOperand { Base: LocalVariable through, Index: null, Scale: 0 } memory] }
                    || !merged.TryGetValue(through, out var split))
                    continue;

                var values = new List<IOperand>();
                for (var i = 0; i < predecessors.Count; i++)
                {
                    var name = $"splitRead{method.Locals.Count}";
                    var value = new LocalVariable(name, new Register(null, name), loaded.Type);
                    method.Locals.Add(value);
                    var read = new Instruction(instruction.Index, OpCode.Move, value,
                        new MemoryOperand(split.Storages[i], null, split.Offsets[i] + memory.Addend, 0, memory.AccessSize)) { NativeAddress = instruction.NativeAddress };
                    InsertBeforeTerminator(predecessors[i], read);
                    definitions[value] = read;
                    values.Add(value);
                }

                var phiName = $"splitPhi{method.Locals.Count}";
                var joined = new LocalVariable(phiName, new Register(null, phiName), loaded.Type);
                method.Locals.Add(joined);
                var join = new Instruction(-1, OpCode.Phi, [joined, .. values]);
                block.Instructions.Insert(phiEnd, join);
                index++;
                instruction.SetOperands(loaded, joined);
                changed = true;
            }
        }

        return SplitPickedOffsets(method) | changed;
    }

    // A field picked by a condition (a CSEL of two field offsets) is an offset merged in a phi and added to one
    // base: [base + phi(48, 56)], or a member of the picked field at phi + 4. Several such selects in a row put
    // the read a few blocks below the phi. Read on each path into the phi's block instead, when nothing between
    // the phi and the read can store or call, and the base is there before the phi.
    private static bool SplitPickedOffsets(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var definitions = graph.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
        var home = new Dictionary<Instruction, Block>();
        foreach (var block in graph.Blocks)
            foreach (var instruction in block.Instructions)
                home[instruction] = block;

        var picked = new Dictionary<LocalVariable, (Block Merge, long[] Offsets)>();
        foreach (var block in graph.Blocks)
        {
            if (block.Predecessors.Count < 2 || block.Predecessors.Distinct().Count() != block.Predecessors.Count)
                continue;
            foreach (var phi in block.Instructions.TakeWhile(i => i.OpCode is OpCode.Phi or OpCode.Nop).Where(i => i.OpCode == OpCode.Phi))
            {
                if (phi.Operands[0] is not LocalVariable offset || phi.Operands.Count - 1 != block.Predecessors.Count)
                    continue;
                var constants = phi.Operands.Skip(1).Select(o => Constant(o, definitions)).ToArray();
                if (constants.All(c => c is >= 0 and < 0x10000) && constants.Distinct().Count() > 1)
                    picked[offset] = (block, constants.Select(c => c!.Value).ToArray());
            }
        }
        if (picked.Count == 0)
            return false;
        foreach (var instruction in graph.Instructions)
            if (instruction is { OpCode: OpCode.Add, Operands: [LocalVariable member, LocalVariable field, Immediate { Value: > 0 and < 0x100 } memberOffset] }
                && picked.TryGetValue(field, out var fieldOffsets))
                picked[member] = (fieldOffsets.Merge, fieldOffsets.Offsets.Select(o => o + memberOffset.Value).ToArray());

        DominatorInfo? dominators = null;
        var changed = false;
        foreach (var block in graph.Blocks.ToList())
        for (var index = 0; index < block.Instructions.Count; index++)
        {
            var load = block.Instructions[index];
            if (load is not { OpCode: OpCode.Move, Operands: [LocalVariable loaded, MemoryOperand { Base: LocalVariable { Type: { } baseType } baseLocal, Index: LocalVariable offsetLocal, Scale: 0 or 1 } memory] }
                || !IsBase(baseType) || !picked.TryGetValue(offsetLocal, out var pick))
                continue;
            var merge = pick.Merge;
            dominators ??= new DominatorInfo(graph);
            // The base must be available on every path into the merge.
            if (definitions.TryGetValue(baseLocal, out var baseDefinition)
                && (!home.TryGetValue(baseDefinition, out var baseBlock) || baseBlock == merge || !dominators.Dominates(baseBlock, merge)))
                continue;
            if (!dominators.Dominates(merge, block) || !Quiet(merge, block, load))
                continue;

            var values = new List<IOperand>();
            for (var i = 0; i < merge.Predecessors.Count; i++)
            {
                var name = $"splitRead{method.Locals.Count}";
                var value = new LocalVariable(name, new Register(null, name), loaded.Type);
                method.Locals.Add(value);
                var read = new Instruction(load.Index, OpCode.Move, value,
                    new MemoryOperand(baseLocal, null, pick.Offsets[i] + memory.Addend, 0, memory.AccessSize)) { NativeAddress = load.NativeAddress };
                InsertBeforeTerminator(merge.Predecessors[i], read);
                home[read] = merge.Predecessors[i];
                values.Add(value);
            }
            var phiName = $"splitPhi{method.Locals.Count}";
            var joined = new LocalVariable(phiName, new Register(null, phiName), loaded.Type);
            method.Locals.Add(joined);
            var join = new Instruction(-1, OpCode.Phi, [joined, .. values]);
            merge.Instructions.Insert(merge.Instructions.FindLastIndex(i => i.OpCode == OpCode.Phi) + 1, join);
            home[join] = merge;
            if (merge == block) index++;
            load.SetOperands(loaded, joined);
            changed = true;
        }
        return changed;

        // Nothing from the merge's phis to the read, on any path between them, stores or calls.
        static bool Quiet(Block merge, Block block, Instruction load)
        {
            static bool Effect(Instruction i) => i.IsCall || i.OpCode is OpCode.IndirectCall or OpCode.IndirectJump or OpCode.Return
                || i.Destination is MemoryOperand or FieldReference or ArrayAccess;
            if (merge == block)
                return !block.Instructions.TakeWhile(i => i != load).Any(Effect);
            if (merge.Instructions.Any(Effect) || block.Instructions.TakeWhile(i => i != load).Any(Effect))
                return false;
            var seen = new HashSet<Block> { merge, block };
            var pending = new Queue<Block>(merge.Successors);
            while (pending.TryDequeue(out var current))
            {
                if (!seen.Add(current))
                    continue;
                if (seen.Count > 24 || current.Instructions.Any(Effect))
                    return false;
                foreach (var successor in current.Successors)
                    pending.Enqueue(successor);
            }
            return true;
        }
    }

    private static long? Constant(IOperand operand, Dictionary<LocalVariable, Instruction> definitions)
    {
        for (var depth = 0; depth < 4 && operand is LocalVariable local && definitions.TryGetValue(local, out var definition)
             && definition is { OpCode: OpCode.Move, Operands: [_, var source] }; depth++)
            operand = source;
        return operand is Immediate immediate ? immediate.Value : null;
    }

    // A class's static storage, or an object whose fields are read (not a value type, pointer or array).
    // An object typed only as Object has no fields to read it as.
    private static bool IsBase(TypeAnalysisContext type) => type is StaticFieldStorageTypeAnalysisContext
        || type is { IsValueType: false, IsInterface: false } and not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext or SzArrayTypeAnalysisContext
            or GenericParameterTypeAnalysisContext or RuntimeClassTypeAnalysisContext or RuntimeMethodInfoAnalysisContext)
        && type.FullName != "System.Object";

    private static void InsertBeforeTerminator(Block block, Instruction instruction)
    {
        var last = block.Instructions.Count - 1;
        if (last >= 0 && block.Instructions[last].OpCode is OpCode.Jump or OpCode.ConditionalJump or OpCode.Switch or OpCode.IndirectJump or OpCode.Return)
            block.Instructions.Insert(last, instruction);
        else
            block.Instructions.Add(instruction);
    }
}
