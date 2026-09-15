using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// A fixed array buffer is null for null/empty arrays, otherwise array + header.
// Resolve only guarded phi edges, not arbitrary pointer-or-null selections.
public static class PinnedArrayRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        if (!cfg.Instructions.Any(i => i.Operands.Any(o => o is MemoryOperand { Index: not null })))
            return;
        var definitions = cfg.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());
        var blocks = cfg.Blocks.SelectMany(b => b.Instructions.Select(i => (i, b))).ToDictionary(p => p.i, p => p.b);
        var header = 4 * method.AppContext.Binary.PointerSizeBytes;

        IOperand Unwrap(IOperand operand)
        {
            var seen = new HashSet<LocalVariable>();
            while (operand is LocalVariable local && seen.Add(local) && definitions.TryGetValue(local, out var def)
                && def is { OpCode: OpCode.Move, Operands: [_, var source] })
                operand = source;
            return operand;
        }

        bool IsZeroEdge(Block predecessor, Block successor, LocalVariable array, bool allowEmpty)
        {
            for (var depth = 0; depth < 8; depth++)
            {
                if (predecessor.Instructions.LastOrDefault() is { OpCode: OpCode.ConditionalJump,
                    Operands: [Block target, var condition] }
                    && Unwrap(condition) is LocalVariable flag && definitions.TryGetValue(flag, out var comparison)
                    && comparison is { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, var value, Immediate { Value: 0 }] }
                    && (comparison.OpCode == OpCode.CheckEqual) == (target == successor))
                {
                    value = Unwrap(value);
                    if (value == array || allowEmpty && (
                        value is ArrayLength length && Unwrap(length.Array) == array
                        || value is MemoryOperand { Base: { } lengthBase, Index: null } memory
                        && memory.Addend == 3 * method.AppContext.Binary.PointerSizeBytes && Unwrap(lengthBase) == array))
                        return true;
                }
                if (predecessor.Predecessors.Count != 1)
                    break;
                successor = predecessor;
                predecessor = predecessor.Predecessors[0];
            }
            return false;
        }

        LocalVariable? Resolve(IOperand operand, int depth)
        {
            if (depth > 8 || Unwrap(operand) is not LocalVariable local || !definitions.TryGetValue(local, out var def))
                return null;
            if (def is { OpCode: OpCode.Add, Operands: [_, var source, Immediate offset] }
                && offset.Value == header && Unwrap(source) is LocalVariable { Type: SzArrayTypeAnalysisContext } array)
                return array;
            if (def.OpCode != OpCode.Phi || !blocks.TryGetValue(def, out var block)
                || def.Operands.Count != block.Predecessors.Count + 1)
                return null;
            LocalVariable? owner = null;
            foreach (var input in def.Operands.Skip(1))
                if (Resolve(input, depth + 1) is { } candidate)
                {
                    if (owner != null && owner != candidate)
                        return null;
                    owner = candidate;
                }
            if (owner == null)
                return null;
            for (var i = 1; i < def.Operands.Count; i++)
            {
                if (Resolve(def.Operands[i], depth + 1) == owner)
                    continue;
                var input = Unwrap(def.Operands[i]);
                if (input is Immediate { Value: 0 })
                {
                    if (!IsZeroEdge(block.Predecessors[i - 1], block, owner, true))
                        return null;
                }
                else if (input != owner || !IsZeroEdge(block.Predecessors[i - 1], block, owner, false))
                    return null;
            }
            return owner;
        }

        var changed = false;
        foreach (var instruction in cfg.Instructions)
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                if (instruction.Operands[i] is not MemoryOperand { Addend: 0, Scale: <= 1 } memory)
                    continue;
                var array = memory.Base == null ? null : Resolve(memory.Base, 0);
                var index = memory.Index;
                if (array == null && memory.Index != null)
                {
                    array = Resolve(memory.Index, 0);
                    index = memory.Base;
                }
                // For byte buffers the native byte displacement is the managed element index.
                if (array?.Type is not SzArrayTypeAnalysisContext { ElementType.FullName: "System.Byte" or "System.SByte" } arrayType
                    || index is not LocalVariable { Type: null } and not LocalVariable { Type.FullName: "System.Int32" or "System.UInt32" or "System.IntPtr" or "System.UIntPtr" })
                    continue;
                if (index is LocalVariable counter)
                    counter.Type ??= method.AppContext.SystemTypes.SystemIntPtrType;
                instruction.SetOperand(i, new ArrayAccess(array, index));
                changed = true;
                if (i == 1 && instruction is { OpCode: OpCode.Move, Destination: LocalVariable result })
                    result.Type = arrayType.ElementType;
            }
        if (changed)
            LocalVariables.ResolveTypesAndFields(method);
    }
}
