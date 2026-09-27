using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Removes pure instructions whose result is never used. This eliminates, among other things, the
/// dead flag/temporary computations the x86 lifter emits eagerly for every comparison - a single
/// <c>cmp</c>/<c>test</c> produces all of CF/OF/SF/ZF/PF plus scratch temporaries, but the branch
/// that follows only consumes one of them.
///
/// Must run while the graph is still in SSA form (every local is assigned exactly once), so that a
/// global use count of zero is sufficient to prove a definition dead. Instructions are turned into
/// nops rather than spliced out; the structural cleanup happens later, out of SSA, where it is safe
/// for phi nodes.
/// </summary>
public static class DeadCodeEliminator
{
    public static void Run(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        Run(cfg);
        var lookups = cfg.Blocks.SelectMany(b => b.Instructions).Where(i => i is
            { OpCode: OpCode.Call, Operands: [Immediate, LocalVariable { Type: StaticFieldStorageTypeAnalysisContext { IsThreadStatic: true } }, ..] }).ToList();
        if (lookups.Count == 0)
            return;
        var uses = CountUses(cfg);
        var removedLookup = false;
        foreach (var instruction in lookups)
        {
            if (uses.ContainsKey((LocalVariable)instruction.Operands[1])
                || !ThreadStaticFieldRecovery.IsLookup(method.AppContext, ((Immediate)instruction.Operands[0]).UnsignedValue))
                continue;
            instruction.OpCode = OpCode.Nop;
            instruction.SetOperands();
            removedLookup = true;
        }
        if (removedLookup)
            Run(cfg);
    }

    public static void Run(ISILControlFlowGraph cfg)
    {
        // Removing a dead definition can make its operands dead in turn, so iterate to a fixpoint.
        // This is monotonic (each pass only nops instructions) and therefore always terminates.
        var changed = true;
        while (changed)
        {
            changed = false;

            var useCounts = CountUses(cfg);

            foreach (var block in cfg.Blocks)
            {
                foreach (var instruction in block.Instructions)
                {
                    if (!IsRemovable(instruction.OpCode))
                        continue;

                    // Only definitions of a register local are candidates. Stores have a memory or
                    // field destination (Destination is not a local) and are never dead.
                    if (instruction.Destination is not LocalVariable destination)
                        continue;

                    if (useCounts.TryGetValue(destination, out var count) && count > 0)
                        continue;

                    instruction.OpCode = OpCode.Nop;
                    instruction.SetOperands();
                    changed = true;
                }
            }
        }
    }

    // Reference counting cannot delete a closed phi/copy cycle. Mark the copies
    // reachable from non-copy uses, retaining calls, stores and address-taken values.
    internal static void RemoveDeadCopyCycles(ISILControlFlowGraph cfg)
    {
        var instructions = cfg.Instructions;
        var copies = instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1)
            .Select(g => g.Single()).Where(i => i.OpCode == OpCode.Phi
                || i is { OpCode: OpCode.Move, Operands: [_, LocalVariable] })
            .ToDictionary(i => (LocalVariable)i.Destination!);
        var copyInstructions = copies.Values.ToHashSet();
        var live = new HashSet<LocalVariable>();
        var pending = new Stack<LocalVariable>(instructions.Where(i => !copyInstructions.Contains(i)).SelectMany(UsedLocals));
        while (pending.TryPop(out var local))
        {
            if (!live.Add(local) || !copies.TryGetValue(local, out var definition))
                continue;
            foreach (var source in UsedLocals(definition))
                pending.Push(source);
        }
        foreach (var (destination, definition) in copies)
            if (!live.Contains(destination))
            {
                definition.OpCode = OpCode.Nop;
                definition.SetOperands();
            }
    }

    private static Dictionary<LocalVariable, int> CountUses(ISILControlFlowGraph cfg)
    {
        var counts = new Dictionary<LocalVariable, int>();

        foreach (var block in cfg.Blocks)
            foreach (var instruction in block.Instructions)
                foreach (var used in UsedLocals(instruction))
                    counts[used] = counts.TryGetValue(used, out var c) ? c + 1 : 1;

        return counts;
    }

    /// <summary>
    /// Every local read by the instruction. The single write position - a plain local destination -
    /// is excluded. Memory and field operands always contribute their address/object locals as
    /// reads, even when they are the destination of a store.
    /// </summary>
    internal static IEnumerable<LocalVariable> UsedLocals(Instruction instruction)
    {
        var destination = instruction.Destination as LocalVariable;

        foreach (var operand in instruction.Operands)
        {
            switch (operand)
            {
                case LocalVariable local when !ReferenceEquals(local, destination):
                    yield return local;
                    break;
                case MemoryOperand memory:
                    if (memory.Base is LocalVariable baseLocal)
                        yield return baseLocal;
                    if (memory.Index is LocalVariable indexLocal)
                        yield return indexLocal;
                    break;
                // A static field access doesn't read the storage pointer it was resolved from, so that
                // pointer (and the class load feeding it) is free to die.
                case FieldReference { IsStatic: false, Local: { } fieldLocal }:
                    yield return fieldLocal;
                    break;
                case AddressOf { Target: FieldReference { IsStatic: false, Local: { } fieldOwner } }:
                    yield return fieldOwner;
                    break;
                // Handing out a slot's address is a read of it as far as we can tell, whatever the callee then does with it.
                case AddressOf { Target: LocalVariable addressed }:
                    yield return addressed;
                    break;
                case AddressOf { Target: ArrayAccess addressedElement }:
                    foreach (var used in ArrayAccessLocals(addressedElement))
                        yield return used;
                    break;
                case ArrayAccess access:
                    foreach (var used in ArrayAccessLocals(access))
                        yield return used;
                    break;
                case ArrayLength { Array: { } lengthArray }:
                    yield return lengthArray;
                    break;
            }
        }
    }

    private static IEnumerable<LocalVariable> ArrayAccessLocals(ArrayAccess access)
    {
        yield return access.Array;

        if (access.Index is LocalVariable index)
            yield return index;
    }

    /// <summary>
    /// Opcodes with no side effects, so removing a never-read result is safe. Calls, stores,
    /// returns and branches are intentionally excluded.
    /// </summary>
    /// <summary>
    /// Out of SSA a local is reused, so a use count no longer proves a definition dead. Recoveries that
    /// run there (runtime check folding, say) leave the metadata reads they replaced behind, e.g. a target
    /// class's typeHierarchyDepth, in a local that is redefined before any read. Find those with liveness.
    /// Only reads of runtime metadata (class and MethodInfo fields, type and method handles) are removed:
    /// they have no effect, so no path the graph does not model (an exception handler) can depend on one.
    /// </summary>
    public static void RemoveDeadMetadataReads(ISILControlFlowGraph cfg)
    {
        var addressTaken = cfg.Instructions.SelectMany(i => i.Operands).OfType<AddressOf>()
            .Select(a => a.Target).OfType<LocalVariable>().ToHashSet();
        for (var changed = true; changed;)
        {
            changed = false;
            var liveIn = cfg.Blocks.ToDictionary(b => b, _ => new HashSet<LocalVariable>());
            for (var grown = true; grown;)
            {
                grown = false;
                foreach (var block in cfg.Blocks.AsEnumerable().Reverse())
                {
                    var live = LiveOut(block, liveIn);
                    for (var i = block.Instructions.Count - 1; i >= 0; i--)
                        Step(block.Instructions[i], live);
                    if (!live.IsSubsetOf(liveIn[block]))
                    {
                        liveIn[block].UnionWith(live);
                        grown = true;
                    }
                }
            }

            foreach (var block in cfg.Blocks)
            {
                var live = LiveOut(block, liveIn);
                for (var i = block.Instructions.Count - 1; i >= 0; i--)
                {
                    var instruction = block.Instructions[i];
                    if (instruction.Destination is LocalVariable destination && !live.Contains(destination)
                        && !addressTaken.Contains(destination) && IsMetadataRead(instruction))
                    {
                        instruction.OpCode = OpCode.Nop;
                        instruction.SetOperands();
                        changed = true;
                        continue;
                    }
                    Step(instruction, live);
                }
            }
        }

        static HashSet<LocalVariable> LiveOut(Block block, Dictionary<Block, HashSet<LocalVariable>> liveIn)
        {
            var live = new HashSet<LocalVariable>();
            foreach (var successor in block.Successors)
                if (liveIn.TryGetValue(successor, out var successorLive))
                    live.UnionWith(successorLive);
            return live;
        }

        static void Step(Instruction instruction, HashSet<LocalVariable> live)
        {
            if (instruction.Destination is LocalVariable defined)
                live.Remove(defined);
            foreach (var used in UsedLocals(instruction))
                live.Add(used);
        }
    }

    private static bool IsMetadataRead(Instruction instruction) => instruction is
    {
        OpCode: OpCode.Move,
        Operands: [LocalVariable, MemoryOperand { Base: LocalVariable { Type: RuntimeClassTypeAnalysisContext or RuntimeMethodInfoAnalysisContext } }
            or TypeAnalysisContext]
    };

    private static bool IsRemovable(OpCode opCode) =>
        opCode switch
        {
            OpCode.IsInstance or OpCode.TryCast or OpCode.ZeroExtend or OpCode.SignExtend or OpCode.Move or OpCode.ConvertNumeric or OpCode.Phi
                or OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.MultiplyHighSigned or OpCode.Divide or OpCode.Modulo
                or OpCode.ShiftLeft or OpCode.ShiftRight
                or OpCode.And or OpCode.Or or OpCode.Xor
                or OpCode.Not or OpCode.Negate or OpCode.LocalAllocate => true,
            >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual => true,
            _ => false
        };
}
