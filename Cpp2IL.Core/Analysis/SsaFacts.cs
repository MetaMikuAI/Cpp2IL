using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Definitions, uses and equality branches of a graph in SSA form, for the passes that prove
/// what an inlined il2cpp runtime check compares before replacing it with the IL it came from.
/// </summary>
internal sealed class SsaFacts
{
    /// <summary>A two-way branch on whether two values are equal, and where each outcome goes.</summary>
    internal sealed record EqualityBranch(Instruction Branch, Instruction Comparison, IOperand Left, IOperand Right,
        Block Taken, Block WhenEqual, Block WhenDifferent);

    private readonly ISILControlFlowGraph _graph;
    private readonly Dictionary<LocalVariable, Instruction> _definitions;
    private readonly Dictionary<LocalVariable, List<Instruction>> _uses = new();

    internal SsaFacts(ISILControlFlowGraph graph)
    {
        _graph = graph;
        _definitions = graph.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());
        foreach (var instruction in graph.Instructions)
        foreach (var local in DeadCodeEliminator.UsedLocals(instruction).Distinct())
        {
            if (!_uses.TryGetValue(local, out var readers)) _uses[local] = readers = [];
            readers.Add(instruction);
        }
    }

    internal IReadOnlyList<Instruction> UsesOf(LocalVariable local) => _uses.TryGetValue(local, out var readers) ? readers : [];

    /// <summary>
    /// The value an operand copies, following register copies, single-input phis and phis
    /// whose every input is the same constant.
    /// </summary>
    internal IOperand Root(IOperand operand) => Root(operand, []);

    private IOperand Root(IOperand operand, HashSet<LocalVariable> seen)
    {
        while (operand is LocalVariable local && seen.Add(local) && _definitions.TryGetValue(local, out var definition))
        {
            if (definition is { OpCode: OpCode.Move or OpCode.Phi, Operands: [_, var source] }
                && source is not (MemoryOperand or FieldReference or ArrayAccess))
                operand = source;
            else if (definition is { OpCode: OpCode.Phi, Operands.Count: > 2 }
                     && definition.Operands.Skip(1).Select(input => Root(input, seen)).Distinct().ToList() is [var constant]
                     && constant is not (LocalVariable or MemoryOperand or FieldReference or ArrayAccess))
                return constant;
            else
                break;
        }
        return operand;
    }

    internal Instruction? DefiningInstruction(LocalVariable local) => _definitions.GetValueOrDefault(local);

    internal Instruction? Definition(IOperand operand)
        => Root(operand) is LocalVariable local && _definitions.TryGetValue(local, out var definition) ? definition : null;

    /// <summary>The address a value was loaded from as [base + offset], giving the root of the base.</summary>
    internal IOperand? LoadBase(IOperand operand, long offset)
        => Definition(operand) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: { } address, Index: null, Addend: var addend }] }
           && addend == offset ? Root(address) : null;

    internal EqualityBranch? EqualityBranchOf(Block block)
    {
        if (block.Successors.Count != 2 || block.Successors[0] == block.Successors[1]
            || block.Instructions.LastOrDefault() is not { OpCode: OpCode.ConditionalJump, Operands: [var target, LocalVariable condition] } branch)
            return null;
        var taken = target switch
        {
            Block targetBlock => targetBlock,
            Instruction instruction => _graph.FindBlockByInstruction(instruction),
            _ => null
        };
        if (taken == null || !block.Successors.Contains(taken) || !_definitions.TryGetValue(condition, out var comparison))
            return null;

        // A logical negation of the comparison flips which way the branch goes.
        var negated = false;
        if (comparison is { OpCode: OpCode.Not, Operands: [_, LocalVariable inner] } && UsesOf(inner).Count == 1
            && _definitions.TryGetValue(inner, out var negatedComparison))
        {
            negated = true;
            comparison = negatedComparison;
        }
        if (comparison is not { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, var left, var right] })
            return null;

        var other = block.Successors.Single(s => s != taken);
        var takenWhenEqual = comparison.OpCode == OpCode.CheckEqual != negated;
        return new(branch, comparison, left, right, taken, takenWhenEqual ? taken : other, takenWhenEqual ? other : taken);
    }

    /// <summary>Whether the branch reads its comparison and nothing else does, so the branch alone decides its fate.</summary>
    internal bool OnlyBranchReads(EqualityBranch branch)
        => branch.Comparison.Destination is LocalVariable result && UsesOf(result).All(u => u == branch.Branch || u.OpCode == OpCode.Not
            && u.Destination is LocalVariable negation && UsesOf(negation).All(n => n == branch.Branch));

    /// <summary>Makes the branch go to the successor other than <paramref name="never"/>; pruning removes the edge.</summary>
    internal static void NeverTake(EqualityBranch branch, Block never)
        => branch.Branch.SetOperand(1, new Immediate(branch.Taken == never ? 0 : 1));

    /// <summary>
    /// Whether the block throws a new exception of the given type before doing anything observable.
    /// A tail-merged throw block may first merge or copy values, which cannot throw; whatever the
    /// lifter left after the throw is unreachable.
    /// </summary>
    internal static bool Throws(Block block, string exceptionName)
    {
        LocalVariable? created = null;
        foreach (var instruction in block.Instructions)
            switch (instruction)
            {
                case { OpCode: OpCode.Nop or OpCode.Phi }:
                case { OpCode: OpCode.Move, Operands: [LocalVariable, var source] } when source is not (MemoryOperand or FieldReference or ArrayAccess):
                    continue;
                case { OpCode: OpCode.Newobj, Operands: [LocalVariable allocated, TypeAnalysisContext type] }
                    when created == null && IsSystemType(type, exceptionName):
                    created = allocated;
                    continue;
                case { OpCode: OpCode.Throw, Operands: [TypeAnalysisContext thrown] }:
                    return created == null && IsSystemType(thrown, exceptionName);
                case { OpCode: OpCode.Throw, Operands: [LocalVariable exception] }:
                    return created != null && exception == created;
                default:
                    return false;
            }
        return false;
    }

    /// <summary>The class a metadata constant denotes, as the analysis operand for Il2CppClass* or its type.</summary>
    internal static TypeAnalysisContext? ClassConstant(IOperand operand) => operand switch
    {
        RuntimeClassTypeAnalysisContext klass => klass.RepresentedType,
        RuntimeMethodInfoAnalysisContext or StaticFieldStorageTypeAnalysisContext => null,
        TypeAnalysisContext type => type,
        _ => null
    };

    private static bool IsSystemType(TypeAnalysisContext type, string name)
        => (type is RuntimeClassTypeAnalysisContext klass ? klass.RepresentedType : type) is { Namespace: "System" } system && system.Name == name;
}
