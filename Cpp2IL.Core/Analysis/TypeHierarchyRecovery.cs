using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// IsInstClass inlines as a depth guard followed by klass->typeHierarchy[targetDepth - 1] == target.
// Recover the complete data-flow pattern, never a load based only on its inferred class-pointer type.
public static class TypeHierarchyRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        // 64-bit class layout used by metadata v29/v31. Do not guess offsets for other runtime layouts.
        if (method.AppContext.Binary.PointerSizeBytes != 8 || method.AppContext.MetadataVersion is not (29 or 31 or 31.1f))
            return;
        Run(method.ControlFlowGraph!, method.Locals, method.AppContext.SystemTypes.SystemBooleanType);
    }

    public static void Run(ISILControlFlowGraph graph, List<LocalVariable> locals, TypeAnalysisContext booleanType)
    {
        var definitions = graph.Instructions.Where(i => i.Destination is LocalVariable)
            .ToDictionary(i => (LocalVariable)i.Destination!, i => i);
        var resolver = new Resolver(definitions);
        var pending = new List<PendingGuard>();
        foreach (var block in graph.Blocks)
        foreach (var comparison in block.Instructions.ToArray())
        {
            if (comparison is not { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, var left, var right] })
                continue;
            // CSET can retain the compare's subtraction when there is no consuming branch.
            if (resolver.Value(right) is Immediate { Value: 0 }
                && resolver.Definition(left) is { OpCode: OpCode.Subtract, Operands: [_, var comparedLeft, var comparedRight] })
            {
                left = comparedLeft;
                right = comparedRight;
            }
            var target = resolver.Value(right) as TypeAnalysisContext;
            var entry = resolver.Value(left) as MemoryOperand?;
            if (target == null || entry == null)
            {
                target = resolver.Value(left) as TypeAnalysisContext;
                entry = resolver.Value(right) as MemoryOperand?;
            }
            if (target == null || target is ReferencedTypeAnalysisContext || target.IsInterface || target.IsValueType)
                continue;

            // The entry is typeHierarchy + depth * 8 - 8, or typeHierarchy indexed by depth - 1.
            IOperand? klass = null;
            if (entry is { Base: { } address, Index: null, Addend: -8 })
            {
                if (resolver.Definition(address) is not { OpCode: OpCode.Add, Operands: [_, var a, var b] }
                    || !resolver.MatchAddress(a, b, target, out klass) && !resolver.MatchAddress(b, a, target, out klass))
                    continue;
            }
            else if (entry is not { Base: { } hierarchy, Index: { } index, Scale: 8, Addend: 0 }
                || !resolver.MatchIndexedAddress(hierarchy, index, target, out klass))
                continue;
            if (resolver.Value(klass!) is not MemoryOperand { Base: LocalVariable receiver, Addend: 0, Index: null, Scale: 0 }
                || receiver.Type == null || receiver.Type.IsValueType || receiver.Type is ReferencedTypeAnalysisContext)
                continue;

            // Only bypass a guard when its failure is the same as the hierarchy check's failure.
            // The full managed test then covers shallow objects too, without an out-of-bounds lookup.
            if (block.Predecessors is [var guard]
                && guard.Instructions.LastOrDefault() is { OpCode: OpCode.ConditionalJump } branch
                && resolver.DepthCondition(branch.Operands[1], klass!, target) is { } enoughBranch
                && Target(graph, branch) is { } taken
                && (enoughBranch ? taken == block : taken != block)
                && guard.Successors.FirstOrDefault(s => s != block) is { } guardFailure
                && (block.Instructions.LastOrDefault() is { OpCode: OpCode.ConditionalJump } checkBranch
                    && ReferenceEquals(resolver.Value(checkBranch.Operands[1]), comparison.Destination)
                    && Failure(graph, block, comparison, checkBranch) is { } checkFailure
                    && resolver.OnlyLookup(block, comparison, checkBranch)
                    && SameFailure(guardFailure, checkFailure, resolver)
                    || SameResultOnMiss(block, guardFailure, comparison, resolver)))
            {
                branch.SetOperand(1, new Immediate(taken == block ? 1 : 0));
            }
            else if (block.Predecessors is [var candidateGuard]
                && candidateGuard.Instructions.LastOrDefault() is { OpCode: OpCode.ConditionalJump } candidateBranch
                && resolver.DepthCondition(candidateBranch.Operands[1], klass!, target) is { } enough
                && Target(graph, candidateBranch) is { } candidateTaken
                && (enough ? candidateTaken == block : candidateTaken != block)
                && candidateGuard.Successors.FirstOrDefault(s => s != block) is { } candidateFailure)
                pending.Add(new PendingGuard(candidateGuard, candidateBranch, block, candidateFailure, target, receiver));

            if (comparison.OpCode == OpCode.CheckEqual)
            {
                comparison.OpCode = OpCode.IsInstance;
                comparison.SetOperands(comparison.Operands[0], target, receiver);
            }
            else
            {
                var result = new LocalVariable($"isInstance{locals.Count}", new Register(null, $"ISINSTANCE{locals.Count}"), booleanType);
                locals.Add(result);
                block.Instructions.Insert(block.Instructions.IndexOf(comparison),
                    new Instruction(comparison.Index, OpCode.IsInstance, result, target, receiver));
                comparison.OpCode = OpCode.CheckEqual;
                comparison.SetOperands(comparison.Operands[0], result, new Immediate(0));
            }
        }
        DeadCodeEliminator.Run(graph);

        // Guards whose arms were not recognised above: now that every lookup is a managed test and its
        // native loads are dead, compare the arms by walking them.
        var bypassed = false;
        foreach (var guard in pending)
        {
            if (guard.Branch.Operands[1] is Immediate || !MissMatchesFailure(guard, resolver)) continue;
            guard.Branch.SetOperand(1, new Immediate(Target(graph, guard.Branch) == guard.Lookup ? 1 : 0));
            bypassed = true;
        }
        if (bypassed) DeadCodeEliminator.Run(graph);
        NarrowSelectedCasts(graph);
    }

    // CSEL lowers `obj as T` to result = match ? obj : null. On the arm where the test holds, the copy of obj
    // is exactly obj as T, so make it that cast. The join with null is then a T, rather than the static type
    // of obj or of a parameter it was passed to, and field offsets on the result resolve against T.
    private static void NarrowSelectedCasts(ISILControlFlowGraph graph)
    {
        var definitions = graph.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());
        IOperand Value(IOperand value)
        {
            for (var i = 0; i < 32 && value is LocalVariable local && definitions.TryGetValue(local, out var definition)
                && definition is { OpCode: OpCode.Move, Operands: [_, var source] }; i++)
                value = source;
            return value;
        }
        (Instruction Test, bool Positive)? Test(IOperand operand, int depth = 0)
        {
            if (depth > 16 || operand is not LocalVariable local || !definitions.TryGetValue(local, out var definition)) return null;
            return definition switch
            {
                { OpCode: OpCode.IsInstance, Operands: [_, TypeAnalysisContext { IsValueType: false }, LocalVariable] } => (definition, true),
                { OpCode: OpCode.Move, Operands: [_, LocalVariable copy] } => Test(copy, depth + 1),
                { OpCode: OpCode.Not, Operands: [_, var inner] } => Test(inner, depth + 1) is { } p ? (p.Test, !p.Positive) : null,
                { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, var inner, Immediate { Value: 0 }] }
                    => Test(inner, depth + 1) is { } p ? (p.Test, p.Positive == (definition.OpCode == OpCode.CheckNotEqual)) : null,
                _ => null,
            };
        }

        foreach (var arm in graph.Blocks)
        {
            if (arm.Predecessors is not [var branchBlock] || arm.Successors is not [var join]
                || branchBlock.Successors.Count != 2
                || branchBlock.Instructions.LastOrDefault() is not { OpCode: OpCode.ConditionalJump, Operands: [Block taken, var condition] }
                || Test(condition) is not { } predicate || predicate.Positive != (taken == arm))
                continue;
            var type = (TypeAnalysisContext)predicate.Test.Operands[1];
            var source = predicate.Test.Operands[2];
            var copies = arm.Instructions.Where(i => i.OpCode is not (OpCode.Nop or OpCode.Jump)).ToArray();
            if (copies is not [{ OpCode: OpCode.Move, Operands: [LocalVariable picked, var copied] } copy]
                || !ReferenceEquals(Value(copied), Value(source)))
                continue;
            var edge = join.Predecessors.IndexOf(arm) + 1;
            var phi = join.Instructions.FirstOrDefault(i => i.OpCode == OpCode.Phi
                && i.Operands.Count == join.Predecessors.Count + 1 && ReferenceEquals(i.Operands[edge], picked));
            if (phi?.Destination is not LocalVariable result
                || !phi.Operands.Skip(1).Where((_, k) => k + 1 != edge).All(o => Value(o) is Immediate { Value: 0 })
                || !Narrows(type, picked.Type) || !Narrows(type, result.Type))
                continue;
            copy.OpCode = OpCode.TryCast;
            copy.SetOperands(picked, type, source);
            var previous = result.Type;
            picked.Type = type;
            result.Type = type;
            // Plain copies of the join took its type from it.
            var pending = new Queue<LocalVariable>([result]);
            while (pending.TryDequeue(out var narrowed))
                foreach (var use in graph.Instructions.Where(i => i is { OpCode: OpCode.Move, Operands: [LocalVariable, LocalVariable from] }
                    && from == narrowed))
                    if (use.Operands[0] is LocalVariable target && target.Type == previous && target.Type != type)
                    {
                        target.Type = type;
                        pending.Enqueue(target);
                    }
        }
    }

    private static bool Narrows(TypeAnalysisContext type, TypeAnalysisContext? current) =>
        current == null || current == type || current is not ReferencedTypeAnalysisContext && type.IsAssignableTo(current);

    private sealed record PendingGuard(Block Guard, Instruction Branch, Block Lookup, Block Failure,
        TypeAnalysisContext Target, LocalVariable Receiver);

    // Bypassing the depth guard sends a shallow object - one that is no instance of the target - through the
    // lookup arm instead of the failure arm. Walk both arms: on the lookup arm every IsInstance of the target on
    // this receiver is false. The arms must reach a common block with equal phi inputs, or equal returns, and
    // execute nothing but local computation on the way, so that no observable effect is added or skipped.
    private static bool MissMatchesFailure(PendingGuard guard, Resolver resolver)
    {
        var miss = ArmWalk.Run(guard.Guard, guard.Lookup, resolver, guard.Target, guard.Receiver);
        var failure = ArmWalk.Run(guard.Guard, guard.Failure, resolver, null, null);
        for (var i = 1; i < miss.Blocks.Count; i++)
        {
            var join = miss.Blocks[i];
            var j = failure.Blocks.IndexOf(join);
            if (j < 0) continue;
            var missEdge = join.Predecessors.IndexOf(miss.Blocks[i - 1]) + 1;
            var failureEdge = join.Predecessors.IndexOf(j == 0 ? guard.Guard : failure.Blocks[j - 1]) + 1;
            if (missEdge == 0 || failureEdge == 0) return false;
            return join.Instructions.Where(p => p.OpCode == OpCode.Phi).All(p => missEdge < p.Operands.Count
                && failureEdge < p.Operands.Count
                && resolver.Same(miss.Evaluate(p.Operands[missEdge]), failure.Evaluate(p.Operands[failureEdge])));
        }
        return miss.Returned is { } missed && failure.Returned is { } failed
            && (missed.Operands.Count == 0 && failed.Operands.Count == 0
                || missed.Operands is [var a] && failed.Operands is [var b]
                && resolver.Same(miss.Evaluate(a), failure.Evaluate(b)));
    }

    // Follows one arm from the guard while it only computes locals and its branches are decided.
    private sealed class ArmWalk
    {
        public readonly List<Block> Blocks = [];
        public Instruction? Returned;
        private readonly Dictionary<LocalVariable, IOperand> _known = new();
        private Resolver _resolver = null!;

        public static ArmWalk Run(Block guard, Block start, Resolver resolver, TypeAnalysisContext? target, LocalVariable? receiver)
        {
            var walk = new ArmWalk { _resolver = resolver };
            var predecessor = guard;
            var block = start;
            while (block != guard && !walk.Blocks.Contains(block) && walk.Blocks.Count < 16)
            {
                walk.Blocks.Add(block);
                var edge = block.Predecessors.IndexOf(predecessor) + 1;
                Block? next = null;
                foreach (var instruction in block.Instructions)
                {
                    if (instruction.OpCode == OpCode.Nop) continue;
                    if (instruction.OpCode == OpCode.Jump)
                    {
                        next = block.Successors is [var only] ? only : null;
                        break;
                    }
                    if (instruction.OpCode == OpCode.Return)
                    {
                        walk.Returned = instruction;
                        return walk;
                    }
                    if (instruction.OpCode == OpCode.ConditionalJump)
                    {
                        if (walk.Evaluate(instruction.Operands[1]) is not Immediate condition || block.Successors.Count != 2
                            || instruction.Operands[0] is not Block taken || !block.Successors.Contains(taken))
                            return walk;
                        next = condition.Value != 0 ? taken : block.Successors.First(s => s != taken);
                        break;
                    }
                    if (instruction.Destination is not LocalVariable destination
                        || instruction.Operands.Any(o => o is MemoryOperand)
                        || !walk.Compute(instruction, destination, edge, target, receiver))
                        return walk;
                }
                if (next == null)
                {
                    if (block.Successors is not [var fallthrough]) return walk;
                    next = fallthrough;
                }
                predecessor = block;
                block = next;
            }
            return walk;
        }

        // Records what a local computation yields on this arm; false for anything that is not one.
        private bool Compute(Instruction instruction, LocalVariable destination, int edge, TypeAnalysisContext? target, LocalVariable? receiver)
        {
            IOperand? value = null;
            switch (instruction.OpCode)
            {
                case OpCode.Phi:
                    if (edge <= 0 || edge >= instruction.Operands.Count) return false;
                    value = Evaluate(instruction.Operands[edge]);
                    break;
                case OpCode.Move:
                    value = Evaluate(instruction.Operands[1]);
                    break;
                case OpCode.IsInstance:
                    if (target != null && receiver != null && instruction.Operands is [_, var tested, var instance]
                        && Equals(_resolver.Value(tested), target) && _resolver.Same(Evaluate(instance), receiver))
                        value = new Immediate(0);
                    break;
                case OpCode.Not when destination.Type?.FullName == "System.Boolean":
                    if (Evaluate(instruction.Operands[1]) is Immediate { Value: 0 or 1 } negated)
                        value = new Immediate(1 - negated.Value);
                    break;
                case OpCode.CheckEqual or OpCode.CheckNotEqual:
                    if (Evaluate(instruction.Operands[1]) is Immediate left && Evaluate(instruction.Operands[2]) is Immediate right)
                        value = new Immediate((left.Value == right.Value) == (instruction.OpCode == OpCode.CheckEqual) ? 1 : 0);
                    break;
                case OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.And or OpCode.Or or OpCode.Xor
                    or OpCode.ShiftLeft or OpCode.ShiftRight or OpCode.Not or OpCode.Negate or OpCode.ZeroExtend
                    or (>= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual):
                    break;
                default:
                    return false;
            }
            if (value != null) _known[destination] = value;
            return true;
        }

        public IOperand Evaluate(IOperand operand) =>
            operand is LocalVariable local && _known.TryGetValue(local, out var value) ? value : _resolver.Value(operand);
    }

    private static Block? Target(ISILControlFlowGraph graph, Instruction branch) => branch.Operands[0] switch
    {
        Block block => block,
        Instruction instruction => graph.FindBlockByInstruction(instruction),
        _ => null
    };

    private static Block? Failure(ISILControlFlowGraph graph, Block block, Instruction comparison, Instruction branch)
    {
        var taken = Target(graph, branch);
        return comparison.OpCode == OpCode.CheckNotEqual ? taken : block.Successors.FirstOrDefault(s => s != taken);
    }

    private static bool SameFailure(Block a, Block b, Resolver resolver)
    {
        a = SkipJumps(a);
        b = SkipJumps(b);
        if (a == b) return true;
        // Two null-producing arms of an 'as' expression may have separate blocks feeding one phi.
        if (a.Successors is not [var merge] || b.Successors is not [var other] || merge != other)
            return false;
        if (a.Instructions.Concat(b.Instructions).Any(i => i.OpCode is not (OpCode.Nop or OpCode.Move or OpCode.Jump)
            || i.OpCode == OpCode.Move && (i.Destination is not LocalVariable || i.Operands[1] is not (Immediate or LocalVariable))))
            return false;
        var ai = merge.Predecessors.IndexOf(a) + 1;
        var bi = merge.Predecessors.IndexOf(b) + 1;
        return ai > 0 && bi > 0 && merge.Instructions.Where(i => i.OpCode == OpCode.Phi)
            .All(i => ai < i.Operands.Count && bi < i.Operands.Count
                && Equals(resolver.Value(i.Operands[ai]), resolver.Value(i.Operands[bi])));
    }

    // A CSET result can go straight to a return or a shared epilogue phi rather than a branch.
    // On a shallow object the managed test is false (true for !=): every observable result must
    // agree with the guard's old failure arm before that guard can be bypassed.
    private static bool SameResultOnMiss(Block lookup, Block failure, Instruction comparison, Resolver resolver)
    {
        failure = SkipJumps(failure);
        if (lookup.Instructions.LastOrDefault() is not { } terminator
            || terminator.OpCode is not (OpCode.Jump or OpCode.Return)
            || !resolver.OnlyLookup(lookup, comparison, terminator, allowCopies: true)
            || failure.Instructions.Any(i => i.OpCode is not (OpCode.Nop or OpCode.Jump or OpCode.Return)
                && !IsLocalCopy(i))) return false;

        var miss = new Immediate(comparison.OpCode == OpCode.CheckEqual ? 0 : 1);
        bool SameValue(IOperand a, IOperand b)
        {
            a = resolver.Value(a);
            return Equals(ReferenceEquals(a, comparison.Destination) ? miss : a, resolver.Value(b));
        }

        if (terminator is { OpCode: OpCode.Return, Operands: [var returned] })
            return failure.Instructions.LastOrDefault() is { OpCode: OpCode.Return, Operands: [var fallback] }
                && SameValue(returned, fallback);

        if (lookup.Successors is not [var merge] || failure.Successors is not [var other] || merge != other)
            return false;
        var li = merge.Predecessors.IndexOf(lookup) + 1;
        var fi = merge.Predecessors.IndexOf(failure) + 1;
        var phis = merge.Instructions.Where(i => i.OpCode == OpCode.Phi).ToArray();
        return li > 0 && fi > 0 && phis.Length > 0
            && phis.All(i => li < i.Operands.Count && fi < i.Operands.Count
                && SameValue(i.Operands[li], i.Operands[fi]));
    }

    private static bool IsLocalCopy(Instruction instruction) => instruction is
        { OpCode: OpCode.Move, Operands: [LocalVariable, Immediate or LocalVariable] };

    private static Block SkipJumps(Block block)
    {
        var seen = new HashSet<Block>();
        while (seen.Add(block) && block.Successors is [var next]
            && block.Instructions.All(i => i.OpCode is OpCode.Nop or OpCode.Jump)) block = next;
        return block;
    }

    private sealed class Resolver(Dictionary<LocalVariable, Instruction> definitions)
    {
        private readonly Dictionary<LocalVariable, IOperand> _values = new();
        private readonly HashSet<LocalVariable> _resolving = new();

        public bool OnlyLookup(Block block, Instruction comparison, Instruction branch, bool allowCopies = false)
        {
            var dependencies = new HashSet<Instruction>();
            void Visit(IOperand operand)
            {
                if (operand is MemoryOperand memory)
                {
                    if (memory.Base != null) Visit(memory.Base);
                    if (memory.Index != null) Visit(memory.Index);
                }
                else if (operand is LocalVariable local && definitions.TryGetValue(local, out var definition)
                    && dependencies.Add(definition))
                    foreach (var source in definition.Sources) Visit(source);
            }
            foreach (var source in comparison.Sources) Visit(source);
            return block.Instructions.All(i => i == comparison || i == branch || i.OpCode == OpCode.Nop
                || allowCopies && IsLocalCopy(i)
                || dependencies.Contains(i) && i.OpCode is OpCode.Move or OpCode.Add or OpCode.ShiftLeft or OpCode.ZeroExtend or OpCode.Subtract);
        }

        public Instruction? Definition(IOperand value)
        {
            for (var i = 0; i < 32 && value is LocalVariable local && definitions.TryGetValue(local, out var instruction); i++)
            {
                if (instruction is { OpCode: OpCode.Move, Operands: [_, LocalVariable copy] }) value = copy;
                else return instruction;
            }
            return null;
        }

        public IOperand Value(IOperand value, int depth = 0)
        {
            if (depth > 32 || value is not LocalVariable local || !definitions.TryGetValue(local, out var instruction)) return value;
            if (_values.TryGetValue(local, out var cached)) return cached;
            if (!_resolving.Add(local)) return value;
            var result = value;
            if (instruction is { OpCode: OpCode.Move, Operands: [_, var source] }) result = Value(source, depth + 1);
            else if (instruction.OpCode == OpCode.Phi && instruction.Operands.Count > 1)
            {
                var values = instruction.Operands.Skip(1).Select(v => Value(v, depth + 1)).ToArray();
                if (values.All(v => Equal(v, values[0]))) result = values[0];
            }
            _resolving.Remove(local);
            return _values[local] = result;
        }

        public bool Same(IOperand a, IOperand b) => Equal(Value(a), Value(b));

        private bool Equal(IOperand a, IOperand b) => a is MemoryOperand x && b is MemoryOperand y
            ? x.Addend == y.Addend && x.Scale == y.Scale && Equals(x.Index, y.Index)
                && x.Base != null && y.Base != null && Equals(Value(x.Base), Value(y.Base))
            : Equals(a, b);

        public bool MatchAddress(IOperand hierarchy, IOperand scaledDepth, TypeAnalysisContext target, out IOperand? klass)
        {
            klass = null;
            return Definition(scaledDepth) is { OpCode: OpCode.ShiftLeft, Operands: [_, var depth, Immediate { Value: 3 }] }
                && MatchHierarchy(hierarchy, depth, target, out klass);
        }

        // LDR Xt, [typeHierarchy, index, LSL #3] with index = targetDepth - 1.
        public bool MatchIndexedAddress(IOperand hierarchy, IOperand index, TypeAnalysisContext target, out IOperand? klass)
        {
            klass = null;
            return Definition(index) is { OpCode: OpCode.Subtract, Operands: [_, var depth, Immediate { Value: 1 }] }
                && MatchHierarchy(hierarchy, depth, target, out klass);
        }

        private bool MatchHierarchy(IOperand hierarchy, IOperand depth, TypeAnalysisContext target, out IOperand? klass)
        {
            klass = null;
            if (Value(hierarchy) is not MemoryOperand { Base: { } baseClass, Addend: 0xC8, Index: null, Scale: 0 }) return false;
            // UXTB/UXTH/UXTW is redundant for Il2CppClass::typeHierarchyDepth, which is uint8_t.
            if (Definition(depth) is { OpCode: OpCode.ZeroExtend, Operands: [_, var narrow, Immediate { Value: 8 or 16 or 32 }] })
                depth = narrow;
            if (!DepthOf(depth, target)) return false;
            klass = baseClass;
            return true;
        }

        private bool DepthOf(IOperand value, IOperand klass) => Value(value) is MemoryOperand
            { Base: { } baseClass, Addend: 0x130, Index: null, Scale: 0 } && Equal(Value(baseClass), Value(klass));

        public bool? DepthCondition(IOperand condition, IOperand klass, TypeAnalysisContext target, int depth = 0)
        {
            if (depth > 16) return null;
            var definition = Definition(condition);
            if (definition is { OpCode: OpCode.Not, Operands: [_, var source] })
                return DepthCondition(source, klass, target, depth + 1) is { } nested ? !nested : null;
            if (definition is not { Operands: [_, var a, var b, ..] }) return null;
            // Hierarchy depths are uint8_t, so signed and explicitly unsigned ordering agree.
            if (definition.Operands.Count > 3 && definition.Operands is not
                [_, _, _, TypeAnalysisContext { FullName: "System.UInt32" or "System.UInt64" }]) return null;
            if (DepthOf(a, klass) && DepthOf(b, target))
                return definition.OpCode switch { OpCode.CheckLess => false, OpCode.CheckGreaterOrEqual => true, _ => null };
            if (DepthOf(b, klass) && DepthOf(a, target))
                return definition.OpCode switch { OpCode.CheckGreater => false, OpCode.CheckLessOrEqual => true, _ => null };
            return null;
        }
    }
}
