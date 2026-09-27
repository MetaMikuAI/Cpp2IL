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

            // Merged addresses: phi of one class's static storage plus a constant per incoming path. Each path
            // may load the storage itself; a class's static storage is the same wherever it is loaded.
            var merged = new Dictionary<LocalVariable, (LocalVariable[] Storages, long[] Offsets)>();
            foreach (var phi in block.Instructions.TakeWhile(i => i.OpCode is OpCode.Phi or OpCode.Nop).Where(i => i.OpCode == OpCode.Phi))
            {
                if (phi.Operands[0] is not LocalVariable address || phi.Operands.Count - 1 != predecessors.Count)
                    continue;
                var storages = new LocalVariable[predecessors.Count];
                var offsets = new long[predecessors.Count];
                string? owner = null;
                var usable = true;
                for (var i = 0; i < offsets.Length; i++)
                {
                    if (phi.Operands[i + 1] is not LocalVariable input || !definitions.TryGetValue(input, out var definition)
                        || definition is not { OpCode: OpCode.Add, Operands: [_, LocalVariable { Type: StaticFieldStorageTypeAnalysisContext storageType } baseLocal, Immediate offset] }
                        || owner != null && owner != storageType.OwnerType.FullName)
                    {
                        usable = false;
                        break;
                    }
                    owner = storageType.OwnerType.FullName;
                    storages[i] = baseLocal;
                    offsets[i] = offset.Value;
                }
                if (usable && offsets.Distinct().Count() > 1)
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

        return changed;
    }

    private static void InsertBeforeTerminator(Block block, Instruction instruction)
    {
        var last = block.Instructions.Count - 1;
        if (last >= 0 && block.Instructions[last].OpCode is OpCode.Jump or OpCode.ConditionalJump or OpCode.Switch or OpCode.IndirectJump or OpCode.Return)
            block.Instructions.Insert(last, instruction);
        else
            block.Instructions.Add(instruction);
    }
}
