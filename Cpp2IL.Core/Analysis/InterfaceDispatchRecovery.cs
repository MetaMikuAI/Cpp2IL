using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Recovers interface calls from GetInterfaceInvokeData which is usually inlined. that method scans klass->interfaceOffsets
// for the declaring interface, indexes the vtable with (entryOffset + slot), or falls back to a slow path
// helper when the scan fails.
public static class InterfaceDispatchRecovery
{
    // Returns a retry for lookups kept alive by guessed downstream call arguments.
    // Invoke it after the caller's normal type/virtual-call resolution pass.
    // Generic virtual calls are only recovered once types are resolved (afterTypeResolution): their parameter
    // types, often a base class, would otherwise claim argument locals before field loads type them exactly.
    public static Action? Run(MethodAnalysisContext method, bool afterTypeResolution = false)
    {
        // offsets below are the 64-bit Il2CppClass layout
        if (method.AppContext.Binary.PointerSizeBytes != 8)
            return null;

        var cfg = method.ControlFlowGraph!;

        var definitions = new Dictionary<LocalVariable, Instruction>();
        var homeBlock = new Dictionary<Instruction, Block>();

        foreach (var block in cfg.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                homeBlock[instruction] = block;
                if (instruction.Destination is LocalVariable destination)
                    definitions[destination] = instruction;
            }
        }

        var matches = new List<Match>();
        var genericHelpers = new List<Instruction>();
        // MethodInfo::virtualMethodPointer, which generic virtual calls go through, exists from metadata v29.
        var genericVirtualLayout = afterTypeResolution && method.AppContext.MetadataVersion >= 29;
        BaseKeyFunctionAddresses? keys = null;

        foreach (var block in cfg.Blocks.ToList())
        {
            foreach (var instruction in block.Instructions.ToList())
            {
                if (instruction.OpCode is not (OpCode.IndirectCall or OpCode.IndirectJump))
                    continue;

                if (MatchDispatch(instruction, definitions, homeBlock) is { } lookups)
                {
                    var invokeDataPhis = lookups.Select(l => l.InvokeDataPhi).ToHashSet();
                    RewriteDispatch(method, instruction, block, lookups[0].Resolved,
                        argument => InvokeDataLoadAddend(definitions, argument, invokeDataPhis), definitions);
                    foreach (var match in lookups)
                    {
                        // The matched native helper takes only obj, interface and slot.
                        while (match.SlowCall.Operands.Count > 5)
                            match.SlowCall.RemoveOperandAt(match.SlowCall.Operands.Count - 1);
                        matches.Add(match);
                    }
                    continue;
                }

                if (genericVirtualLayout && MatchGenericVirtualDispatch(instruction, definitions, homeBlock, ReachesGenericVirtualMethod) is { } generic)
                {
                    RewriteDispatch(method, instruction, block, generic.Resolved,
                        argument => GenericVirtualLoadAddend(definitions, argument, generic.Helper), definitions);
                    genericHelpers.Add(generic.Helper);
                    if (generic.Lookup is { } lookup)
                    {
                        while (lookup.SlowCall.Operands.Count > 5)
                            lookup.SlowCall.RemoveOperandAt(lookup.SlowCall.Operands.Count - 1);
                        matches.Add(lookup);
                    }
                }
            }
        }

        if (matches.Count == 0 && genericHelpers.Count == 0) return null;
        Cleanup();
        return Cleanup;

        // Locating the helper disassembles the runtime, so only a matching call shape asks for it.
        bool ReachesGenericVirtualMethod(ulong address)
        {
            keys ??= method.AppContext.GetOrCreateKeyFunctionAddresses();
            return keys.CallReaches(address, keys.il2cpp_vm_runtime_get_generic_virtual_method);
        }

        void Cleanup()
        {
            // Rewrite all dispatches before checking whether lookup values are dead.
            // Retrying after normal type resolution lets newly resolved virtual calls
            // release their guessed arguments without changing type-inference order.
            CallArgumentTrimmer.Run(method, preserveGenericMetadata: true);
            DeadCodeEliminator.RemoveDeadCopyCycles(cfg);
            DeadCodeEliminator.Run(method);
            if (RemoveDeadGenericVirtualLookups(cfg, genericHelpers))
                DeadCodeEliminator.Run(method);
            DominatorInfo? dominators = null;
            foreach (var match in matches)
            {
                var klass = Definition(definitions, match.KlassLocal);
                if (!TryExciseLookup(cfg, match, homeBlock, ref dominators)) continue;
                if (match.Resolved.FullName == "System.IDisposable::Dispose" && match.Dispatch.NativeAddress != 0
                    && klass is { NativeAddress: not 0, Operands: [_, MemoryOperand { Base: LocalVariable receiver }] })
                    method.NativeDisposals.Add(new(match.Dispatch, klass.NativeAddress, receiver.Register.Name));
            }
            DeadCodeEliminator.Run(method);
        }
    }

    private const long VTableOffset = 0x138;
    private const int InvokeDataShift = 4; // sizeof(VirtualInvokeData) == 16

    internal record struct Match(
        MethodAnalysisContext Resolved,
        Instruction InvokeDataPhi,
        Block Merge,
        Instruction SlowCall,
        LocalVariable KlassLocal,
        Instruction Dispatch,
        TypeAnalysisContext Interface,
        int Slot);

    // Returns every lookup the dispatch calls through: one, or several when the compiler merged
    // identical interface calls into a single indirect call behind a phi of their methodPtr loads.
    private static List<Match>? MatchDispatch(Instruction dispatch, Dictionary<LocalVariable, Instruction> definitions, Dictionary<Instruction, Block> homeBlock)
    {
        // the call target loads VirtualInvokeData::methodPtr, separately or folded in
        var targetLoad = dispatch.Operands[0] switch
        {
            MemoryOperand folded => folded,
            LocalVariable target when Definition(definitions, target) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand loaded] } => loaded,
            _ => default(MemoryOperand?)
        };

        if (targetLoad is { Index: null, Scale: 0, Addend: 0, Base: LocalVariable invokeData })
            return Definition(definitions, invokeData) is { } phi && MatchLookup(phi, dispatch, definitions, homeBlock) is { } match ? [match] : null;

        return dispatch.Operands[0] is LocalVariable merged ? MatchSharedDispatch(dispatch, merged, definitions, homeBlock) : null;
    }

    // Every incoming methodPtr load must come from a recognized lookup of the same interface method. A merged
    // call to different methods, or through any other value, is not one managed call and is left alone.
    private static List<Match>? MatchSharedDispatch(Instruction dispatch, LocalVariable target, Dictionary<LocalVariable, Instruction> definitions, Dictionary<Instruction, Block> homeBlock)
    {
        var loads = new List<Instruction>();
        if (Definition(definitions, target) is not { OpCode: OpCode.Phi } || !CollectPhiInputs(definitions, target, loads, []) || loads.Count < 2)
            return null;

        var matches = new List<Match>();
        foreach (var load in loads)
        {
            if (load is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable invokeData }] }
                || Definition(definitions, invokeData) is not { } phi
                || MatchLookup(phi, dispatch, definitions, homeBlock) is not { } match)
                return null;

            if (matches.Count > 0 && (match.Slot != matches[0].Slot || match.Interface.FullName != matches[0].Interface.FullName))
                return null;

            if (matches.All(m => !ReferenceEquals(m.InvokeDataPhi, phi)))
                matches.Add(match);
        }

        return matches;
    }

    // Collects the non-phi definitions feeding a phi web, failing on any value without a visible definition.
    private static bool CollectPhiInputs(Dictionary<LocalVariable, Instruction> definitions, LocalVariable local, List<Instruction> inputs, HashSet<LocalVariable> visited)
    {
        if (!visited.Add(local))
            return true;

        if (Definition(definitions, local) is not { } definition)
            return false;

        if (definition.OpCode != OpCode.Phi)
        {
            if (!inputs.Contains(definition))
                inputs.Add(definition);
            return true;
        }

        foreach (var operand in definition.Operands.Skip(1))
            if (operand is not LocalVariable source || !CollectPhiInputs(definitions, source, inputs, visited))
                return false;

        return true;
    }

    // A generic interface method is looked up with method->klass and method->slot read at run time, so
    // genericMethod stands in for the constant interface and slot of an ordinary interface call.
    private static Match? MatchLookup(Instruction phi, Instruction dispatch, Dictionary<LocalVariable, Instruction> definitions, Dictionary<Instruction, Block> homeBlock,
        RuntimeMethodInfoAnalysisContext? genericMethod = null)
    {
        if (phi is not { OpCode: OpCode.Phi, Operands: [_, LocalVariable first, LocalVariable second] })
            return null;

        var firstDefinition = Definition(definitions, first);
        var secondDefinition = Definition(definitions, second);

        var slowCall = firstDefinition is { OpCode: OpCode.Call } 
            ? firstDefinition
            : secondDefinition is { OpCode: OpCode.Call } ? secondDefinition : null;
        var vtableEntry = ReferenceEquals(slowCall, firstDefinition) ? secondDefinition : firstDefinition;

        // slow path is GetInterfaceInvokeDataFromVTableSlowPath(obj, interface, slot), never resolved
        if (slowCall is not { Operands: [Immediate, _, _, LocalVariable interfaceArg, LocalVariable slotArg, ..] })
            return null;

        var slotLocal = genericMethod != null ? slotArg : null;
        var declaringInterface = ResolveConstant(definitions, interfaceArg) as TypeAnalysisContext;
        if (declaringInterface == null && genericMethod != null && IsMethodInfoField(definitions, interfaceArg, genericMethod, MethodInfoKlassOffset))
            declaringInterface = genericMethod.RepresentedMethod.DeclaringType;
        if (declaringInterface == null)
            return null;

        if (declaringInterface is RuntimeClassTypeAnalysisContext runtimeClass)
            declaringInterface = runtimeClass.RepresentedType;

        if (declaringInterface is RuntimeMethodInfoAnalysisContext
            || !(declaringInterface is GenericInstanceTypeAnalysisContext { GenericType.IsInterface: true } || declaringInterface.IsInterface))
            return null;

        int slot;
        if (ResolveConstant(definitions, slotArg) is Immediate { Value: >= 0 and <= ushort.MaxValue } slotImmediate)
            slot = (int)slotImmediate.Value;
        else if (genericMethod != null && SlotOf(genericMethod.RepresentedMethod) is { } genericSlot && IsMethodInfoField(definitions, slotArg, genericMethod, MethodInfoSlotOffset))
            slot = genericSlot;
        else
            return null;

        // fast path computes klass + vtableOffset + ((entryOffset + slot) << 4) (the +slot folds away for slot 0)
        if (MatchVTableEntryChain(definitions, vtableEntry, slot, slotLocal) is not { } klassLocal)
            return null;

        if (ResolveInterfaceSlot(declaringInterface, slot) is not { } resolved)
            return null;

        if (!homeBlock.TryGetValue(phi, out var merge))
            return null;

        return new Match(resolved, phi, merge, slowCall, klassLocal, dispatch, declaringInterface, slot);
    }

    // 8 for a VirtualInvokeData::method load off one of the lookups (the hidden MethodInfo argument),
    // 0 for a stale methodPtr load, null for anything else. Merged calls pass these through phis.
    private static long? InvokeDataLoadAddend(Dictionary<LocalVariable, Instruction> definitions, LocalVariable argument, HashSet<Instruction> invokeDataPhis)
    {
        var inputs = new List<Instruction>();
        if (!CollectPhiInputs(definitions, argument, inputs, []))
            return null;

        long? addend = null;
        foreach (var input in inputs)
        {
            if (input is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Base: LocalVariable loadBase } load] }
                || Definition(definitions, loadBase) is not { } loadBaseDefinition
                || !invokeDataPhis.Contains(loadBaseDefinition)
                || load.Addend is not (0 or 8)
                || (addend != null && addend != load.Addend))
                return null;
            addend = load.Addend;
        }

        return addend;
    }

    // slotLocal, when given, is the run-time slot value the lookup may add instead of the constant slot.
    internal static LocalVariable? MatchVTableEntryChain(Dictionary<LocalVariable, Instruction> definitions, Instruction? vtableEntry, int slot, LocalVariable? slotLocal = null)
    {
        // Both klass + (scaledSlot + header) and (klass + scaledSlot) + header
        // are emitted by native compilers. Keep the same scale/slot/load proof.
        var headerOutside = vtableEntry is { OpCode: OpCode.Add, Operands: [_, LocalVariable, Immediate { Value: VTableOffset }] };
        if (headerOutside)
            vtableEntry = ChaseCopies(definitions, (LocalVariable)vtableEntry!.Operands[1]);
        if (vtableEntry is not { OpCode: OpCode.Add, Operands: [_, LocalVariable addLeft, LocalVariable addRight] })
            return null;

        var (klassCandidate, sum) = ChaseCopies(definitions, addRight) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Addend: 0 }] }
            ? (addRight, addLeft)
            : (addLeft, addRight);
        if (ChaseCopies(definitions, klassCandidate) is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable }] })
            return null;

        var scaled = ChaseCopies(definitions, sum);
        if (!headerOutside)
        {
            if (scaled is not { OpCode: OpCode.Add, Operands: [_, LocalVariable shifted, Immediate { Value: VTableOffset }] })
                return null;
            scaled = ChaseCopies(definitions, shifted);
        }
        if (scaled is not { OpCode: OpCode.ShiftLeft, Operands: [_, LocalVariable index, Immediate { Value: InvokeDataShift }] })
            return null;

        var entryOffset = ChaseCopies(definitions, index);
        if (entryOffset is { OpCode: OpCode.SignExtend or OpCode.ZeroExtend, Operands: [_, LocalVariable narrow, Immediate { Value: 32 }] })
            entryOffset = ChaseCopies(definitions, narrow);
        if (entryOffset is { OpCode: OpCode.Add, Operands: [_, LocalVariable beforeSlot, Immediate slotAddend] })
        {
            if (slotAddend.Value != slot)
                return null;
            entryOffset = ChaseCopies(definitions, beforeSlot);
        }
        else if (slotLocal != null && entryOffset is { OpCode: OpCode.Add, Operands: [_, LocalVariable left, LocalVariable right] }
                 && (SameValue(definitions, left, slotLocal) || SameValue(definitions, right, slotLocal)))
            entryOffset = ChaseCopies(definitions, SameValue(definitions, right, slotLocal) ? left : right);
        else if (slot != 0)
            return null;
        if (entryOffset is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: not null }] })
            return null;
        return klassCandidate;
    }

    // Guard removal leaves single-input phis; they are copies, not unresolved joins.
    internal static IOperand? ResolveConstant(Dictionary<LocalVariable, Instruction> definitions, IOperand operand)
    {
        if (operand is TypeAnalysisContext or Immediate) return operand;
        return operand is LocalVariable local && ChaseCopies(definitions, local) is
            { OpCode: OpCode.Move or OpCode.Phi, Operands: [_, var constant] }
            && constant is TypeAnalysisContext or Immediate
            ? constant : null;
    }

    private static Instruction? Definition(Dictionary<LocalVariable, Instruction> definitions, LocalVariable local)
        => definitions.TryGetValue(local, out var definition) ? definition : null;

    private static Instruction? ChaseCopies(Dictionary<LocalVariable, Instruction> definitions, LocalVariable local)
    {
        var visited = new HashSet<LocalVariable>();

        while (visited.Add(local))
        {
            if (Definition(definitions, local) is not { } definition)
                return null;

            if (definition is { OpCode: OpCode.Move or OpCode.Phi, Operands: [_, LocalVariable source] })
            {
                local = source;
                continue;
            }

            return definition;
        }

        return null;
    }

    private static MethodAnalysisContext? ResolveInterfaceSlot(TypeAnalysisContext declaringInterface, int slot)
    {
        if (declaringInterface is GenericInstanceTypeAnalysisContext genericInstance)
        {
            var baseMethod = genericInstance.GenericType.Methods.FirstOrDefault(m => m.Definition?.slot == slot);
            return baseMethod == null ? null : new ConcreteGenericMethodAnalysisContext(baseMethod, genericInstance.GenericArguments, []);
        }

        return declaringInterface.Methods.FirstOrDefault(m => m.Definition?.slot == slot);
    }

    // hiddenLoadAddend classifies an argument as the hidden MethodInfo (8), a stale methodPtr (0) or neither (null).
    private static void RewriteDispatch(MethodAnalysisContext method, Instruction dispatch, Block block, MethodAnalysisContext resolved,
        Func<LocalVariable, long?> hiddenLoadAddend, Dictionary<LocalVariable, Instruction> definitions)
    {
        var callingConventions = resolved.AppContext.InstructionSet.CallingConventionResolver;
        var isTailCall = dispatch.OpCode == OpCode.IndirectJump;

        // an IndirectJump's return register operand is a stale use rather than a return slot, so rebuild from scratch
        if (isTailCall)
        {
            var operands = new List<IOperand> { resolved };

            if (!resolved.IsVoid)
                operands.Add(new LocalVariable("interfaceTailCallResult", callingConventions?.ReturnRegister(resolved) ?? new Register(null, "rax")));

            operands.AddRange(dispatch.Operands.Skip(2));
            dispatch.SetOperands(operands);
        }
        else
        {
            if (resolved.IsVoid)
                dispatch.RemoveOperandAt(1);
            else if (callingConventions is { }
                     && dispatch.ImplicitDefinition is { } returnDefinition
                     && returnDefinition.Number == callingConventions.ReturnRegister(resolved).Number
                     && method.Locals.FirstOrDefault(local => local.Register == returnDefinition) is { } floatResult)
                dispatch.SetOperand(1, floatResult);

            dispatch.SetOperand(0, resolved);
        }

        dispatch.OpCode = resolved.IsVoid ? OpCode.CallVoid : OpCode.Call;
        callingConventions?.RemapRawArguments(dispatch, resolved);

        // name [phi+8] as the hidden MethodInfo param, like ResolveVirtualCalls. A tail call's target
        // register doubles as an argument slot, so a stale [phi] load can turn up as an argument too,
        // and gets a placeholder so the VirtualInvokeData pointer still dies.
        var assembly = resolved.DeclaringType?.DeclaringAssembly ?? method.DeclaringType?.DeclaringAssembly;
        for (var i = 1; i < dispatch.Operands.Count; i++)
        {
            if (dispatch.Operands[i] is not LocalVariable argument)
                continue;

            var addend = hiddenLoadAddend(argument);
            if (addend == 8 && assembly != null)
                dispatch.SetOperand(i, new RuntimeMethodInfoAnalysisContext(resolved, assembly));
            else if (addend == 0)
                dispatch.SetOperand(i, new Immediate(0));
        }

        if (isTailCall)
        {
            var returnOperands = !method.IsVoid && !resolved.IsVoid
                ? new List<IOperand> { dispatch.Operands[1] }
                : [];

            block.AddInstruction(new Instruction(-1, OpCode.Return, returnOperands));
            block.CalculateBlockType();
        }
    }

    // Bailing here is fine, it just leaves the (already resolved) call with dead lookup around it
    private static bool TryExciseLookup(ISILControlFlowGraph cfg, Match match, Dictionary<Instruction, Block> homeBlock, ref DominatorInfo? dominators)
    {
        var merge = match.Merge;

        if (!homeBlock.TryGetValue(match.SlowCall, out var slowBlock) || !cfg.Blocks.Contains(slowBlock))
            return false;

        // The class pointer may be hoisted above unrelated branches or reused by several
        // dispatches. The merge's immediate dominator bounds this lookup, not that load.
        dominators ??= new DominatorInfo(cfg);
        if (!dominators.ImmediateDominators.TryGetValue(merge, out var head)
            || head == null || !cfg.Blocks.Contains(head))
            return false;

        if (!TryCollectRegion(cfg, head, merge, out var region) || !region.Contains(slowBlock))
            return false;

        if (!RegionIsSideEffectFree(region, match.SlowCall) || AnyValueEscapes(cfg, region, merge))
            return false;

        if (!MergePhisAreDead(cfg, merge, region, out var removable, out var forwarded))
            return false;

        foreach (var instruction in removable)
        {
            instruction.OpCode = OpCode.Nop;
            instruction.SetOperands();
        }

        // Only the head reaches the merge afterwards, so a phi of one outside value is a copy of it.
        foreach (var (phi, value) in forwarded)
        {
            phi.OpCode = OpCode.Move;
            phi.SetOperands(phi.Operands[0], value);
        }

        foreach (var successor in head.Successors)
            successor.Predecessors.Remove(head);
        head.Successors.Clear();
        head.Successors.Add(merge);

        var terminator = head.Instructions[^1];
        if (terminator.OpCode is OpCode.Jump or OpCode.ConditionalJump)
        {
            terminator.OpCode = OpCode.Jump;
            terminator.SetOperands(merge);
        }
        else
            head.AddInstruction(new Instruction(-1, OpCode.Jump, merge));

        head.CalculateBlockType();

        merge.Predecessors.RemoveAll(region.Contains);
        merge.Predecessors.Add(head);

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
        return true;
    }

    // The region has to be closed, so nothing else may enter or leave it
    private static bool TryCollectRegion(ISILControlFlowGraph cfg, Block head, Block merge, out HashSet<Block> region)
    {
        region = [];

        var queue = new Queue<Block>(merge.Predecessors);

        while (queue.Count > 0)
        {
            var block = queue.Dequeue();

            if (block == head)
                continue;

            if (block == merge || block == cfg.EntryBlock || block == cfg.ExitBlock || region.Count > 64)
                return false;

            if (!region.Add(block))
                continue;

            foreach (var predecessor in block.Predecessors)
                queue.Enqueue(predecessor);
        }

        if (region.Count == 0)
            return false;

        var collected = region;
        foreach (var block in collected)
        {
            if (block.Predecessors.Any(p => p != head && !collected.Contains(p)))
                return false;
            if (block.Successors.Any(s => s != merge && !collected.Contains(s)))
                return false;
        }

        // we rewrite the head's terminator, so it can't branch anywhere else
        return head.Successors.All(s => s == merge || collected.Contains(s));
    }

    private static bool RegionIsSideEffectFree(HashSet<Block> region, Instruction slowCall)
    {
        foreach (var block in region)
        {
            foreach (var instruction in block.Instructions)
            {
                if (ReferenceEquals(instruction, slowCall))
                    continue;

                var harmless = instruction.OpCode switch
                {
                    OpCode.Nop or OpCode.Jump or OpCode.ConditionalJump or OpCode.Phi => true,
                    OpCode.Move or OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide or OpCode.Modulo
                        or OpCode.ShiftLeft or OpCode.ShiftRight or OpCode.SignExtend or OpCode.ZeroExtend or OpCode.And or OpCode.Or or OpCode.Xor
                        or OpCode.Not or OpCode.Negate
                        or (>= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual)
                        => instruction.Destination is LocalVariable,
                    _ => false,
                };

                if (!harmless)
                    return false;
            }
        }

        return true;
    }

    // Merge phis are exempt, their deadness gets checked separately
    private static bool AnyValueEscapes(ISILControlFlowGraph cfg, HashSet<Block> region, Block merge)
    {
        var regionDefs = new HashSet<LocalVariable>();
        foreach (var block in region)
            foreach (var instruction in block.Instructions)
                if (instruction.Destination is LocalVariable destination)
                    regionDefs.Add(destination);

        foreach (var block in cfg.Blocks)
        {
            if (region.Contains(block))
                continue;

            foreach (var instruction in block.Instructions)
            {
                if (instruction.OpCode == OpCode.Phi && block == merge)
                    continue;

                if (Uses(instruction, regionDefs))
                    return true;
            }
        }

        return false;
    }

    // They may only feed loads off the VirtualInvokeData pointer, which must themselves be dead, or
    // carry one value from outside the region along every path, which the head then passes on directly
    private static bool MergePhisAreDead(ISILControlFlowGraph cfg, Block merge, HashSet<Block> region, out List<Instruction> removable,
        out List<(Instruction Phi, IOperand Value)> forwarded)
    {
        removable = [];
        forwarded = [];
        var regionDefinitions = region.SelectMany(b => b.Instructions).Select(i => i.Destination).OfType<LocalVariable>().ToHashSet();

        var useSites = new Dictionary<LocalVariable, List<Instruction>>();
        foreach (var block in cfg.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                foreach (var used in UsedLocals(instruction))
                {
                    if (!useSites.TryGetValue(used, out var sites))
                        useSites[used] = sites = [];
                    sites.Add(instruction);
                }
            }
        }

        foreach (var phi in merge.Instructions)
        {
            if (phi.OpCode != OpCode.Phi)
                continue;

            if (phi.Operands[0] is not LocalVariable phiDest)
                return false;

            var incoming = phi.Operands.Skip(1).Where(o => !ReferenceEquals(o, phiDest)).Distinct().ToList();
            if (incoming is [var single] && !(single is LocalVariable singleLocal && regionDefinitions.Contains(singleLocal))
                && useSites.ContainsKey(phiDest))
            {
                forwarded.Add((phi, single));
                continue;
            }

            foreach (var use in useSites.TryGetValue(phiDest, out var phiUses) ? phiUses : [])
            {
                if (use is not { OpCode: OpCode.Move, Operands: [LocalVariable loaded, MemoryOperand] }
                    || (useSites.TryGetValue(loaded, out var loadUses) && loadUses.Count > 0))
                    return false;

                removable.Add(use);
            }

            removable.Add(phi);
        }

        return true;
    }

    // 64-bit MethodInfo layout of metadata v29+, the first with MethodInfo::virtualMethodPointer
    private const long MethodInfoVirtualMethodPointerOffset = 0x8;
    private const long MethodInfoKlassOffset = 0x20;
    private const long MethodInfoSlotOffset = 0x50;
    private const long InvokeDataMethodOffset = 0x8; // VirtualInvokeData::method

    internal record struct GenericVirtualMatch(MethodAnalysisContext Resolved, Instruction Helper, Match? Lookup);

    // Calls to a generic virtual method ask Runtime::GetGenericVirtualMethod for the override inflated from the
    // receiver's vtable method and call its virtualMethodPointer with it as the hidden MethodInfo:
    //   target = GetGenericVirtualMethod(obj->klass->vtable[method->slot].method, method)
    //   target->virtualMethodPointer(obj, args..., target)
    // For a generic interface method the vtable method comes from the interface lookup of method->klass instead.
    internal static GenericVirtualMatch? MatchGenericVirtualDispatch(Instruction dispatch, Dictionary<LocalVariable, Instruction> definitions,
        Dictionary<Instruction, Block> homeBlock, Func<ulong, bool> reachesGenericVirtualMethod)
    {
        var targetLoad = dispatch.Operands[0] switch
        {
            MemoryOperand folded => folded,
            LocalVariable target when ChaseCopies(definitions, target) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand loaded] } => loaded,
            _ => default(MemoryOperand?)
        };

        if (targetLoad is not { Index: null, Scale: 0, Addend: MethodInfoVirtualMethodPointerOffset, Base: LocalVariable targetMethod }
            || ChaseCopies(definitions, targetMethod) is not { OpCode: OpCode.Call, Operands: [Immediate helperAddress, LocalVariable, LocalVariable vtableMethod, var genericArgument, ..] } helper
            || AsMethodInfo(definitions, genericArgument) is not { } genericMethod
            || genericMethod.RepresentedMethod is not { IsStatic: false } resolved
            || dispatch.Operands is not [_, _, LocalVariable receiver, ..])
            return null;

        // The slot only matters where native code folded it into a constant; a slot read from the MethodInfo is proof enough.
        var slot = SlotOf(resolved) ?? -1;

        Match? lookup = null;
        var vtableLoad = ChaseCopies(definitions, vtableMethod);
        if (vtableLoad is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Addend: InvokeDataMethodOffset, Base: LocalVariable invokeData }] }
            && Definition(definitions, invokeData) is { OpCode: OpCode.Phi } invokeDataPhi)
        {
            if (!resolved.DeclaringType!.IsInterface && resolved.DeclaringType is not GenericInstanceTypeAnalysisContext { GenericType.IsInterface: true })
                return null;
            if (MatchLookup(invokeDataPhi, dispatch, definitions, homeBlock, genericMethod) is not { } match || match.Slot != slot)
                return null;
            lookup = match;
        }
        else if (!IsVTableSlotMethod(definitions, vtableLoad, receiver, genericMethod, slot))
            return null;

        return reachesGenericVirtualMethod((ulong)helperAddress.Value) ? new GenericVirtualMatch(resolved, helper, lookup) : null;
    }

    // klass->vtable[method->slot].method, with klass loaded from the receiver of the dispatch
    private static bool IsVTableSlotMethod(Dictionary<LocalVariable, Instruction> definitions, Instruction? vtableLoad, LocalVariable receiver,
        RuntimeMethodInfoAnalysisContext genericMethod, int slot)
    {
        if (vtableLoad is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Base: LocalVariable entry } load] })
            return false;

        LocalVariable klass;
        if (load.Addend == VTableOffset + InvokeDataMethodOffset
            && ChaseCopies(definitions, entry) is { OpCode: OpCode.Add, Operands: [_, LocalVariable left, LocalVariable right] })
        {
            var leftScaled = ChaseCopies(definitions, left) is { OpCode: OpCode.ShiftLeft };
            var scaled = ChaseCopies(definitions, leftScaled ? left : right);
            klass = leftScaled ? right : left;
            if (scaled is not { OpCode: OpCode.ShiftLeft, Operands: [_, LocalVariable index, Immediate { Value: InvokeDataShift }] })
                return false;

            var slotValue = ChaseCopies(definitions, index);
            if (slotValue is { OpCode: OpCode.ZeroExtend or OpCode.SignExtend, Operands: [_, LocalVariable narrow, _] })
                slotValue = ChaseCopies(definitions, narrow);
            var isSlot = slotValue switch
            {
                { OpCode: OpCode.Move, Operands: [_, Immediate { Value: var value }] } => slot >= 0 && value == slot,
                { OpCode: OpCode.Move, Operands: [LocalVariable slotDestination, MemoryOperand] } => IsMethodInfoField(definitions, slotDestination, genericMethod, MethodInfoSlotOffset),
                _ => false,
            };
            if (!isSlot)
                return false;
        }
        // native code folded a constant slot into the load
        else if (slot >= 0 && load.Addend == VTableOffset + InvokeDataMethodOffset + ((long)slot << InvokeDataShift))
            klass = entry;
        else
            return false;

        return ChaseCopies(definitions, klass) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable klassSource }] }
               && SameValue(definitions, klassSource, receiver);
    }

    // value is a load of the given MethodInfo field of genericMethod
    private static bool IsMethodInfoField(Dictionary<LocalVariable, Instruction> definitions, LocalVariable value, RuntimeMethodInfoAnalysisContext genericMethod, long offset)
        => ChaseCopies(definitions, value) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Base: LocalVariable methodInfo } field] }
           && field.Addend == offset
           && AsMethodInfo(definitions, methodInfo) is { } loaded
           && ReferenceEquals(loaded.RepresentedMethod, genericMethod.RepresentedMethod);

    // An inflated method has no definition of its own; its slot is the generic definition's.
    private static int? SlotOf(MethodAnalysisContext method)
        => (method is ConcreteGenericMethodAnalysisContext { BaseMethodContext: { } baseMethod } ? baseMethod : method).Definition?.slot;

    private static RuntimeMethodInfoAnalysisContext? AsMethodInfo(Dictionary<LocalVariable, Instruction> definitions, IOperand operand)
        => operand as RuntimeMethodInfoAnalysisContext ?? ResolveConstant(definitions, operand) as RuntimeMethodInfoAnalysisContext;

    // Both locals hold the same SSA value, seen through copies and single-input phis.
    private static bool SameValue(Dictionary<LocalVariable, Instruction> definitions, LocalVariable a, LocalVariable b)
        => ReferenceEquals(CopyRoot(definitions, a), CopyRoot(definitions, b));

    private static LocalVariable CopyRoot(Dictionary<LocalVariable, Instruction> definitions, LocalVariable local)
    {
        var visited = new HashSet<LocalVariable>();
        while (visited.Add(local) && Definition(definitions, local) is { OpCode: OpCode.Move or OpCode.Phi, Operands: [_, LocalVariable source] })
            local = source;
        return local;
    }

    // The helper's result is the hidden MethodInfo (8 in RewriteDispatch terms); a stale load of its
    // virtualMethodPointer, which a tail call's target register can leave as an argument, is 0.
    private static long? GenericVirtualLoadAddend(Dictionary<LocalVariable, Instruction> definitions, LocalVariable argument, Instruction helper)
    {
        var result = (LocalVariable)helper.Operands[1];
        if (SameValue(definitions, argument, result))
            return 8;

        return ChaseCopies(definitions, argument) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Addend: MethodInfoVirtualMethodPointerOffset, Base: LocalVariable loadBase }] }
               && SameValue(definitions, loadBase, result)
            ? 0
            : null;
    }

    // GetGenericVirtualMethod only computes the MethodInfo the recovered call now names.
    private static bool RemoveDeadGenericVirtualLookups(ISILControlFlowGraph cfg, List<Instruction> helpers)
    {
        if (helpers.Count == 0)
            return false;

        var used = cfg.Blocks.SelectMany(b => b.Instructions).SelectMany(UsedLocals).ToHashSet();
        var removed = false;
        foreach (var helper in helpers)
        {
            if (helper.OpCode != OpCode.Call || helper.Operands[1] is not LocalVariable result || used.Contains(result))
                continue;

            helper.OpCode = OpCode.Nop;
            helper.SetOperands();
            removed = true;
        }

        return removed;
    }

    private static bool Uses(Instruction instruction, HashSet<LocalVariable> candidates)
        => UsedLocals(instruction).Any(candidates.Contains);

    // Type resolution may have replaced raw memory operands with fields/arrays.
    private static IEnumerable<LocalVariable> UsedLocals(Instruction instruction)
        => DeadCodeEliminator.UsedLocals(instruction);
}
