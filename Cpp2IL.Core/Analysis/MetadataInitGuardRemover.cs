using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Removes the IL2CPP runtime-metadata initialization guards the compiler emits near the top of
/// (almost) every method, plus il2cpp_runtime_class_init blocks.
/// </summary>
public static class MetadataInitGuardRemover
{
    private const string InitializeRuntimeMetadata = "il2cpp_codegen_initialize_runtime_metadata";
    private const string InitializeMethod = "il2cpp_codegen_initialize_method";
    private const string ClassInitExport = "il2cpp_runtime_class_init_export";
    private const string ClassInitActual = "il2cpp_runtime_class_init_actual";
    private const string ClassInitCodegen = "il2cpp_codegen_runtime_class_init";

    // Byte holding Il2CppClass's bitfield, of which bit 0 is initialized_and_no_error.
    // TODO this is almost certainly not correct on every version... but which?
    private const long InitialisedFlagOffset64 = 0x135;
    private const long InitialisedFlagOffset32 = 0xBD;

    // Offset of Il2CppClass::cctor_finished_or_no_cctor on the 64-bit metadata v29/v31 layout.
    private const long CctorFinishedOffset64 = 0xE0;

    // Offset of MethodInfo::rgctx_data
    private const long MethodRgctxOffset64 = 0x38;
    private const long MethodRgctxOffset32 = 0x1C;

    public static void Run(MethodAnalysisContext method)
        => Run(method.ControlFlowGraph!, method.AppContext.Binary.is32Bit ? InitialisedFlagOffset32 : InitialisedFlagOffset64);

    // Rewrite any metadata init calls we didn't remove into movs.
    public static void RewriteUnguardedInits(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Call || instruction.Operands is not [StringLiteral { Value: InitializeRuntimeMetadata or InitializeMethod }, var result, var handle, ..])
                continue;

            instruction.OpCode = OpCode.Move;
            instruction.SetOperands(result, handle);
        }
    }
    
    // Removes the lazy-init guards protecting a generic method's inlined RGCTX metadata lookups.
    public static void RunRgctx(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        var rgctxOffset = method.AppContext.Binary.is32Bit ? MethodRgctxOffset32 : MethodRgctxOffset64;

        var removedAny = false;

        foreach (var guard in cfg.Blocks.ToList())
            removedAny |= TryRemoveRgctxGuard(cfg, guard, rgctxOffset);

        if (removedAny)
            DeadCodeEliminator.Run(cfg);
    }

    private static bool TryRemoveRgctxGuard(ISILControlFlowGraph cfg, Block guard, long rgctxOffset)
    {
        if (guard.BlockType != BlockType.TwoWay || guard.Successors.Count != 2
            || guard.Instructions.Count == 0 || guard.Instructions[^1].OpCode != OpCode.ConditionalJump)
            return false;

        var isRgctxGuard = guard.Instructions.Any(i =>
            i.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual
            && (IsRgctxLoad(i.Operands[1], rgctxOffset) && IsZero(i.Operands[2])
                || IsRgctxLoad(i.Operands[2], rgctxOffset) && IsZero(i.Operands[1])));

        if (!isRgctxGuard)
            return false;

        var first = guard.Successors[0];
        var second = guard.Successors[1];

        // treat region calls as init boilerplate, exactly as the class-init flag test does
        return TryExcise(cfg, guard, first, second, true)
            || TryExcise(cfg, guard, second, first, true);
    }

    private static bool IsRgctxLoad(IOperand operand, long rgctxOffset) =>
        operand is MemoryOperand { Index: null, Scale: 0, Base: LocalVariable { Type: RuntimeMethodInfoAnalysisContext } } memory
        && memory.Addend == rgctxOffset;

    private static bool IsZero(IOperand operand) => operand is Immediate { Value: 0 };

    public static void Run(ISILControlFlowGraph cfg, long initialisedFlagOffset)
    {
        var removedAny = false;

        foreach (var guard in cfg.Blocks.ToList())
            removedAny |= TryRemoveGuard(cfg, guard, initialisedFlagOffset);

        removedAny |= RemoveBareClassInitCalls(cfg);

        if (removedAny)
            DeadCodeEliminator.Run(cfg);
    }

    // wasm keeps the initialized-flag check inside the class-init function, so callers make bare unguarded
    // calls with no region to excise (just drop the call)
    private static bool RemoveBareClassInitCalls(ISILControlFlowGraph cfg)
    {
        var removedAny = false;

        foreach (var block in cfg.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                if (!instruction.IsCall
                    || instruction.Operands[0] is not StringLiteral { Value: ClassInitExport or ClassInitActual or ClassInitCodegen })
                    continue;

                instruction.OpCode = OpCode.Nop;
                instruction.SetOperands();
                removedAny = true;
            }
        }

        return removedAny;
    }

    private static bool TryRemoveGuard(ISILControlFlowGraph cfg, Block guard, long initialisedFlagOffset)
    {
        if (guard.BlockType != BlockType.TwoWay || guard.Successors.Count != 2
            || guard.Instructions.Count == 0 || guard.Instructions[^1].OpCode != OpCode.ConditionalJump)
            return false;

        // see if we're checking Il2CppClass::initialized_and_no_error
        // that means this is runtime_init boilerplate and we can drop the block
        var initialisedFlagTest = guard.Instructions.Any(i => i.OpCode == OpCode.And
            && i.Operands is [_, MemoryOperand { Index: null, Scale: 0, Base: LocalVariable } flag, { } mask]
            && flag.Addend == initialisedFlagOffset && IsOne(mask));

        // Either successor could be the init entry; the other is then the merge.
        var first = guard.Successors[0];
        var second = guard.Successors[1];

        return TryExcise(cfg, guard, first, second, initialisedFlagTest)
            || TryExcise(cfg, guard, second, first, initialisedFlagTest);
    }

    // SSA keeps the flag load separate from its bit test. Only accept a typed class
    // pointer and a single initializer call on the same pointer; never arbitrary calls.
    public static void RunSsaClassGuards(MethodAnalysisContext method)
    {
        if (method.AppContext.Binary.PointerSizeBytes != 8 || method.AppContext.MetadataVersion is not (29 or 31 or 31.1f))
            return;
        RunSsaClassGuards(method.ControlFlowGraph!, InitialisedFlagOffset64);
    }

    internal static void RunSsaClassGuards(ISILControlFlowGraph cfg, long flagOffset)
    {
        var definitions = cfg.Instructions.Where(i => i.Destination is LocalVariable)
            .ToDictionary(i => (LocalVariable)i.Destination!, i => i);
        foreach (var guard in cfg.Blocks.ToArray())
        {
            if (guard.Instructions.LastOrDefault() is not { OpCode: OpCode.ConditionalJump, Operands: [Block taken, var condition] }
                || guard.Successors.Count != 2)
                continue;
            var initOnTrue = false;
            var seen = new HashSet<LocalVariable>();
            while (condition is LocalVariable local && seen.Add(local) && definitions.TryGetValue(local, out var definition))
            {
                if (definition is { OpCode: OpCode.Move, Operands: [_, var source] })
                    condition = source;
                else if (definition is { OpCode: OpCode.Not, Operands: [_, var negated] })
                {
                    initOnTrue = !initOnTrue;
                    condition = negated;
                }
                else if (definition is { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, var compared, Immediate { Value: 0 }] })
                {
                    if (definition.OpCode == OpCode.CheckEqual) initOnTrue = !initOnTrue;
                    condition = compared;
                }
                else break;
            }
            if (condition is not LocalVariable tested || !definitions.TryGetValue(tested, out var mask)
                || mask is not { OpCode: OpCode.And, Operands: [_, var flag, Immediate { Value: 1 }] }
                || Value(flag, definitions) is not MemoryOperand { Base: LocalVariable klass, Index: null, Scale: 0 } memory
                || memory.Addend != flagOffset || klass.Type is not RuntimeClassTypeAnalysisContext)
                continue;
            var init = initOnTrue ? taken : guard.Successors.First(s => s != taken);
            var merge = guard.Successors.First(s => s != init);
            if (init.Successors.Count != 1 || init.Successors[0] != merge)
                continue;
            var calls = init.Instructions.Where(i => i.IsCall).ToArray();
            if (calls is not [{ OpCode: OpCode.Call, Operands: [Immediate, _, var argument, ..] }]
                || init.Instructions.Any(i => i.OpCode == OpCode.Move && i.Operands[0] is not LocalVariable)
                || !ReferenceEquals(Value(argument, definitions), Value(klass, definitions)))
                continue;
            TryExcise(cfg, guard, init, merge, true);
        }
        DeadCodeEliminator.Run(cfg);
    }

    // IL2CPP_RUNTIME_CLASS_INIT(klass) is `if (!klass->cctor_finished_or_no_cctor) il2cpp_runtime_class_init(klass)`.
    // Run excises it when the not-finished arm is only the initializer and rejoins. The compiler often also
    // duplicates the continuation into that arm (reloads after the opaque call, a tail call), so the arms
    // never rejoin. That arm assumes nothing about memory once the initializer has run, while the finished
    // arm may reuse values loaded before the test; managed code initializes the class implicitly. With the
    // initializer call already dropped, the not-finished arm is the continuation: branch to it unconditionally.
    public static void FoldCctorGuards(MethodAnalysisContext method)
    {
        if (method.AppContext.Binary.PointerSizeBytes != 8 || method.AppContext.MetadataVersion is not (29 or 31 or 31.1f))
            return;
        FoldCctorGuards(method.ControlFlowGraph!, CctorFinishedOffset64);
    }

    internal static bool FoldCctorGuards(ISILControlFlowGraph cfg, long finishedOffset)
    {
        var definitions = cfg.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());
        var folded = false;
        foreach (var guard in cfg.Blocks)
        {
            if (guard.Instructions.LastOrDefault() is not { OpCode: OpCode.ConditionalJump, Operands: [Block taken, var condition] } branch
                || guard.Successors.Count != 2 || !guard.Successors.Contains(taken))
                continue;
            // A conditional jump is taken on a non-zero condition; track whether that means "finished".
            var takenWhenFinished = true;
            var seen = new HashSet<LocalVariable>();
            while (condition is LocalVariable local && seen.Add(local) && definitions.TryGetValue(local, out var definition))
            {
                if (definition is { OpCode: OpCode.Move, Operands: [_, var source] })
                    condition = source;
                else if (definition is { OpCode: OpCode.Not, Operands: [_, var negated] } && IsBoolean(local))
                {
                    takenWhenFinished = !takenWhenFinished;
                    condition = negated;
                }
                else if (definition is { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, var compared, Immediate { Value: 0 }] })
                {
                    if (definition.OpCode == OpCode.CheckEqual) takenWhenFinished = !takenWhenFinished;
                    condition = compared;
                }
                else break;
            }
            if (Value(condition, definitions) is not MemoryOperand
                { Base: LocalVariable { Type: RuntimeClassTypeAnalysisContext }, Index: null, Scale: 0, AccessSize: 0 or 4 } memory
                || memory.Addend != finishedOffset)
                continue;
            var init = takenWhenFinished ? guard.Successors.First(s => s != taken) : taken;
            // Run dropped every initializer call it could name; an unnamed call heading the arm may be one it could not.
            if (FirstCall(init) is { Operands: [not StringLiteral and not MethodAnalysisContext, ..] })
                continue;
            branch.SetOperand(1, new Immediate(init == taken ? 1 : 0));
            folded = true;
        }
        return folded;
    }

    private static bool IsBoolean(LocalVariable local) => local.Type?.FullName == "System.Boolean";

    // The first call on the straight-line code that starts an arm, across blocks split at calls.
    private static Instruction? FirstCall(Block block)
    {
        var seen = new HashSet<Block>();
        while (seen.Add(block))
        {
            if (block.Instructions.FirstOrDefault(i => i.IsCall) is { } call)
                return call;
            if (block.Successors is not [var next] || next.Predecessors.Count != 1)
                return null;
            block = next;
        }
        return null;
    }

    private static IOperand Value(IOperand value, Dictionary<LocalVariable, Instruction> definitions)
    {
        var seen = new HashSet<LocalVariable>();
        while (value is LocalVariable local && seen.Add(local) && definitions.TryGetValue(local, out var definition)
            && definition is { OpCode: OpCode.Move, Operands: [_, var source] })
            value = source;
        return value;
    }

    private static bool IsOne(IOperand operand) => operand is Immediate { Value: 1 };

    private static bool TryExcise(ISILControlFlowGraph cfg, Block guard, Block initEntry, Block merge, bool initialisedFlagTest)
    {
        if (merge == cfg.EntryBlock || merge == cfg.ExitBlock)
            return false;

        if (!TryCollectRegion(cfg, guard, initEntry, merge, initialisedFlagTest, out var region))
            return false;

        Excise(cfg, guard, initEntry, merge, region);
        return true;
    }

    private static bool TryCollectRegion(ISILControlFlowGraph cfg, Block guard, Block initEntry, Block merge,
        bool initialisedFlagTest, out HashSet<Block> region)
    {
        region = [];

        if (initEntry == merge || initEntry == guard)
            return false;

        var sawMetadataInit = false;
        var sawClassInit = false;
        var sawFlagStore = false;
        var reconverges = false;

        var queue = new Queue<Block>();
        queue.Enqueue(initEntry);

        while (queue.Count > 0)
        {
            var block = queue.Dequeue();

            if (block == merge)
            {
                reconverges = true;
                continue;
            }

            // The region must not run into the method boundary or loop back through the guard.
            if (block == cfg.EntryBlock || block == cfg.ExitBlock || block == guard)
                return false;

            if (!region.Add(block))
                continue;

            if (!ClassifyBlock(block, initialisedFlagTest, ref sawMetadataInit, ref sawClassInit, ref sawFlagStore))
                return false;

            foreach (var successor in block.Successors)
                queue.Enqueue(successor);
        }

        if (!reconverges || !(sawClassInit || (sawMetadataInit && sawFlagStore)))
            return false;

        var collected = region;
        foreach (var block in collected)
        {
            if (block.Predecessors.Any(predecessor => predecessor != guard && !collected.Contains(predecessor)))
                return false;
            if (block.Successors.Any(successor => successor != merge && !collected.Contains(successor)))
                return false;
        }

        return true;
    }

    // A region block is acceptable only if every instruction is intra-region control flow, an init
    // call, the flag store, or otherwise side-effect-free (writes a local, not memory). A managed call
    // or any other store would have an effect we cannot silently drop, so it disqualifies the region.
    private static bool ClassifyBlock(Block block, bool initialisedFlagTest, ref bool sawMetadataInit, ref bool sawClassInit, ref bool sawFlagStore)
    {
        foreach (var instruction in block.Instructions)
        {
            switch (instruction.OpCode)
            {
                case OpCode.Jump:
                    break;

                // Behind an initialized_and_no_error test the callee is the class initializer, even if we didn't resolve it.
                // If we didn't, that's fine, just skip.
                case OpCode.Call or OpCode.CallVoid when initialisedFlagTest:
                    sawClassInit = true;
                    break;

                case OpCode.Call or OpCode.CallVoid:
                    if (instruction.Operands is not [StringLiteral { Value: var name }, ..])
                        return false;

                    if (name is InitializeRuntimeMetadata or InitializeMethod)
                        sawMetadataInit = true;
                    else if (name is ClassInitExport or ClassInitActual or ClassInitCodegen)
                        sawClassInit = true;
                    else
                        return false;

                    break;

                case OpCode.Move when instruction.Operands is [MemoryOperand { IsConstant: true }, _]:
                    sawFlagStore = true;
                    break;

                default:
                    if (!IsSideEffectFree(instruction))
                        return false;
                    break;
            }
        }

        return true;
    }

    // True for instructions that only compute a value into a local (or do nothing). A store - any
    // instruction whose destination operand is a memory or field reference rather than a local - is
    // excluded, as is anything that transfers control or merges values (phi/return/indirect).
    private static bool IsSideEffectFree(Instruction instruction) =>
        instruction.OpCode switch
        {
            OpCode.Nop => true,
            OpCode.Move or OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide or OpCode.Modulo
                or OpCode.ShiftLeft or OpCode.ShiftRight or OpCode.And or OpCode.Or or OpCode.Xor
                or OpCode.Not or OpCode.Negate
                or (>= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual)
                => instruction.Operands is [LocalVariable, ..],
            _ => false,
        };

    internal static void Excise(ISILControlFlowGraph cfg, Block guard, Block initEntry, Block merge, HashSet<Block> region)
    {
        // 1. Repair the merge's phis: drop the inputs from the region's back-edges.
        for (var i = merge.Predecessors.Count - 1; i >= 0; i--)
        {
            if (!region.Contains(merge.Predecessors[i]))
                continue;

            foreach (var phi in merge.Instructions)
                if (phi.OpCode == OpCode.Phi && 1 + i < phi.Operands.Count)
                    phi.RemoveOperandAt(1 + i);

            merge.Predecessors.RemoveAt(i);
        }

        // 2. Fold the guard so it goes straight to the merge.
        guard.Successors.Remove(initEntry);
        initEntry.Predecessors.Remove(guard);

        var terminator = guard.Instructions[^1];
        terminator.OpCode = OpCode.Jump;
        terminator.SetOperands(merge);
        guard.CalculateBlockType();

        // 3. Delete the region. 
        foreach (var block in region)
        {
            foreach (var successor in block.Successors)
                successor.Predecessors.Remove(block);
            foreach (var predecessor in block.Predecessors)
                predecessor.Successors.Remove(block);

            block.Successors.Clear();
            block.Predecessors.Clear();
            cfg.Blocks.Remove(block);
        }
    }
}
