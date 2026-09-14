using System.Collections.Generic;
using System.Linq;
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
            if (target == null || target is ReferencedTypeAnalysisContext || target.IsInterface || target.IsValueType
                || entry is not { Base: { } address, Index: null, Addend: -8 })
                continue;

            var add = resolver.Definition(address);
            if (add is not { OpCode: OpCode.Add, Operands: [_, var a, var b] })
                continue;
            if (!resolver.MatchAddress(a, b, target, out var klass)
                && !resolver.MatchAddress(b, a, target, out klass))
                continue;
            if (resolver.Value(klass!) is not MemoryOperand { Base: LocalVariable receiver, Addend: 0, Index: null, Scale: 0 }
                || receiver.Type == null || receiver.Type.IsValueType || receiver.Type is ReferencedTypeAnalysisContext)
                continue;

            // Only bypass a guard when its failure is the same as the hierarchy check's failure.
            // The full managed test then covers shallow objects too, without an out-of-bounds lookup.
            if (block.Predecessors is [var guard]
                && guard.Instructions.LastOrDefault() is { OpCode: OpCode.ConditionalJump } branch
                && block.Instructions.LastOrDefault() is { OpCode: OpCode.ConditionalJump } checkBranch
                && ReferenceEquals(resolver.Value(checkBranch.Operands[1]), comparison.Destination)
                && resolver.DepthCondition(branch.Operands[1], klass!, target) is { } enoughBranch
                && Target(graph, branch) is { } taken
                && (enoughBranch ? taken == block : taken != block)
                && guard.Successors.FirstOrDefault(s => s != block) is { } guardFailure
                && Failure(graph, block, comparison, checkBranch) is { } checkFailure
                && resolver.OnlyLookup(block, comparison, checkBranch)
                && SameFailure(guardFailure, checkFailure, resolver))
            {
                branch.SetOperand(1, new Immediate(taken == block ? 1 : 0));
            }

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

        public bool OnlyLookup(Block block, Instruction comparison, Instruction branch)
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

        private bool Equal(IOperand a, IOperand b) => a is MemoryOperand x && b is MemoryOperand y
            ? x.Addend == y.Addend && x.Scale == y.Scale && Equals(x.Index, y.Index)
                && x.Base != null && y.Base != null && Equals(Value(x.Base), Value(y.Base))
            : Equals(a, b);

        public bool MatchAddress(IOperand hierarchy, IOperand scaledDepth, TypeAnalysisContext target, out IOperand? klass)
        {
            klass = null;
            if (Value(hierarchy) is not MemoryOperand { Base: { } baseClass, Addend: 0xC8, Index: null, Scale: 0 }
                || Definition(scaledDepth) is not { OpCode: OpCode.ShiftLeft, Operands: [_, var depth, Immediate { Value: 3 }] }) return false;
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
            if (definition is not { Operands: [_, var a, var b] }) return null;
            if (DepthOf(a, klass) && DepthOf(b, target))
                return definition.OpCode switch { OpCode.CheckLess => false, OpCode.CheckGreaterOrEqual => true, _ => null };
            if (DepthOf(b, klass) && DepthOf(a, target))
                return definition.OpCode switch { OpCode.CheckGreater => false, OpCode.CheckLessOrEqual => true, _ => null };
            return null;
        }
    }
}
