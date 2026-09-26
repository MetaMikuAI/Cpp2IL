using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Folds a branch that is left with nothing to decide once the runtime checks it guarded are gone.
/// A class-initialisation guard (<c>klass->cctor_finished == 0</c>) whose arm also carried duplicated
/// code, or the repeated type check native code runs to compute a write barrier's value, keeps its
/// branch after the call and the value are removed: both successors now reach the same block without
/// executing anything.
///
/// Such a branch is folded only when its condition is built purely from runtime type metadata - class
/// pointers, loads from an <c>Il2CppClass</c> and <c>isinst</c> results - so a branch on program data
/// whose arms lost their values stays visible. Runs out of SSA, where an empty arm has no copies left.
/// </summary>
public static class RuntimeCheckBranchFolder
{
    private const int MaxDepth = 16;

    public static bool Run(MethodAnalysisContext method) => Run(method.ControlFlowGraph!);

    internal static bool Run(ISILControlFlowGraph graph)
    {
        var definitions = new Dictionary<LocalVariable, List<Instruction>>();
        foreach (var instruction in graph.Instructions)
            if (instruction.Destination is LocalVariable local)
            {
                if (!definitions.TryGetValue(local, out var list))
                    definitions[local] = list = [];
                list.Add(instruction);
            }

        var changed = false;
        foreach (var block in graph.Blocks.ToList())
        {
            if (block.Successors.Count != 2 || block.Instructions.LastOrDefault() is not
                    { OpCode: OpCode.ConditionalJump, Operands: [_, var condition] } branch)
                continue;

            var landing = Landing(block.Successors[0], block);
            if (landing == null || landing != Landing(block.Successors[1], block)
                || !IsRuntimeMetadata(condition, definitions, MaxDepth))
                continue;

            var arms = block.Successors.Where(s => s != landing).ToList();
            foreach (var successor in block.Successors)
                successor.Predecessors.Remove(block);
            block.Successors.Clear();
            block.Successors.Add(landing);
            landing.Predecessors.Add(block);
            branch.OpCode = OpCode.Jump;
            branch.SetOperands(landing);
            block.CalculateBlockType();

            // The empty arms nothing else reaches are dead now.
            var pending = new Stack<Block>(arms);
            while (pending.TryPop(out var arm))
            {
                if (arm.Predecessors.Count != 0 || arm == graph.EntryBlock || arm == graph.ExitBlock)
                    continue;
                foreach (var successor in arm.Successors)
                {
                    successor.Predecessors.Remove(arm);
                    if (successor != landing)
                        pending.Push(successor);
                }
                arm.Successors.Clear();
                graph.Blocks.Remove(arm);
            }

            changed = true;
        }

        return changed;
    }

    // Where control ends up from successor, passing through blocks that do nothing but continue.
    private static Block? Landing(Block successor, Block branch)
    {
        var current = successor;
        for (var steps = 0; steps < 8; steps++)
        {
            if (current == branch || current.Successors.Count != 1
                || current.Instructions.Any(i => i.OpCode is not (OpCode.Nop or OpCode.Jump)))
                return current == branch ? null : current;
            current = current.Successors[0];
        }
        return null;
    }

    private static bool IsRuntimeMetadata(IOperand operand, Dictionary<LocalVariable, List<Instruction>> definitions, int depth)
    {
        switch (operand)
        {
            case Immediate:
            case RuntimeClassTypeAnalysisContext:
            case LocalVariable { Type: RuntimeClassTypeAnalysisContext }:
            // a field of the class structure itself, such as cctor_finished or the hierarchy depth
            case MemoryOperand { Base: LocalVariable { Type: RuntimeClassTypeAnalysisContext } }:
                return true;
            case LocalVariable local when depth > 0
                                          && definitions.TryGetValue(local, out var defs) && defs.Count == 1:
                var definition = defs[0];
                if (definition.OpCode == OpCode.IsInstance)
                    return true;
                if (definition.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual
                    && definition.Operands.Count == 3
                    && IsObjectClassComparison(definition.Operands[1], definition.Operands[2], definitions))
                    return true;
                return definition.OpCode is OpCode.Move or OpCode.Not or OpCode.And or OpCode.Or or OpCode.Xor
                           or (>= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual)
                       && definition.Operands.Skip(1).All(source => IsRuntimeMetadata(source, definitions, depth - 1));
            default:
                return false;
        }
    }

    // An object's header word against a class constant: the exact-type test sealed classes compile to.
    private static bool IsObjectClassComparison(IOperand left, IOperand right, Dictionary<LocalVariable, List<Instruction>> definitions) =>
        IsObjectHeader(left, definitions) && right is RuntimeClassTypeAnalysisContext
        || IsObjectHeader(right, definitions) && left is RuntimeClassTypeAnalysisContext;

    private static bool IsObjectHeader(IOperand operand, Dictionary<LocalVariable, List<Instruction>> definitions) => operand switch
    {
        MemoryOperand { Base: LocalVariable, Index: null, Addend: 0 } => true,
        LocalVariable local => definitions.TryGetValue(local, out var defs) && defs.Count == 1
                               && defs[0] is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: LocalVariable, Index: null, Addend: 0 }] },
        _ => false
    };
}
