using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Removes ARM64 stack-protector checks. The prologue copies the guard value at [TPIDR_EL0 + 0x28]
/// into the frame and the epilogue compares that copy with the guard, calling __stack_chk_fail when
/// they differ. They differ only if the frame was overwritten, which the method's IL cannot do, so the
/// branch to __stack_chk_fail is never taken.
/// </summary>
public static class StackProtectorRecovery
{
    private const string FailFunction = "__stack_chk_fail";

    // Bionic keeps the stack guard in thread-pointer slot 5 (TLS_SLOT_STACK_GUARD).
    private const long GuardOffset = 0x28;

    // MRS Xt, TPIDR_EL0 with Rt cleared, and the bits shared by every MRS encoding.
    private const uint ReadThreadPointer = 0xD53BD040;
    private const uint MrsMask = 0xFFF00000;
    private const uint Mrs = 0xD5300000;

    public static void Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet || method.ControlFlowGraph is not { } graph
            || !ReadsOnlyThreadPointer(method.RawBytes.AsSpan()))
            return;

        var binary = method.AppContext.Binary;
        Run(graph, target => Arm64ImportResolver.Resolve(binary, target) == FailFunction);
    }

    /// <summary>
    /// Folds the checks branching to calls of the stack-protector failure function, given how to recognise it,
    /// and prunes what only those branches reached. The graph must be in SSA form.
    /// </summary>
    internal static bool Run(ISILControlFlowGraph graph, Func<ulong, bool> isFailFunction)
    {
        var failures = graph.Blocks.Where(block => CallsFailFunction(block, isFailFunction)).ToList();
        if (failures.Count == 0)
            return false;

        var definitions = graph.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());

        var folded = false;
        foreach (var failure in failures)
        foreach (var check in failure.Predecessors.Distinct().ToList())
            folded |= TryFoldCheck(graph, check, failure, definitions);

        return folded && ConstantBranchFolder.PruneSsa(graph);
    }

    // The lifted SYSREG value is TPIDR_EL0 only if the method reads no other system register.
    internal static bool ReadsOnlyThreadPointer(ReadOnlySpan<byte> bytes)
    {
        for (var offset = 0; offset + 4 <= bytes.Length; offset += 4)
        {
            var word = BinaryPrimitives.ReadUInt32LittleEndian(bytes.Slice(offset, 4));
            if ((word & MrsMask) == Mrs && (word & ~0x1Fu) != ReadThreadPointer)
                return false;
        }

        return true;
    }

    // __stack_chk_fail does not return, so whatever the lifter placed after the call is unreachable.
    private static bool CallsFailFunction(Block block, Func<ulong, bool> isFailFunction)
        => block.Instructions.FirstOrDefault(i => i.OpCode != OpCode.Nop) is { IsCall: true, Operands: [Immediate target, ..] }
           && isFailFunction(target.UnsignedValue);

    private static bool TryFoldCheck(ISILControlFlowGraph graph, Block check, Block failure,
        Dictionary<LocalVariable, Instruction> definitions)
    {
        if (check.Successors.Count != 2 || check.Successors[0] == check.Successors[1]
            || check.Instructions.LastOrDefault() is not { OpCode: OpCode.ConditionalJump, Operands: [var target, LocalVariable condition] } branch)
            return false;

        var taken = target switch
        {
            Block block => block,
            Instruction instruction => graph.FindBlockByInstruction(instruction),
            _ => null
        };
        if (taken == null || !check.Successors.Contains(taken))
            return false;

        // A logical negation of the comparison result flips which way the branch goes.
        var negated = false;
        if (definitions.TryGetValue(condition, out var definition) && definition is { OpCode: OpCode.Not, Operands: [_, LocalVariable inner] }
            && definitions.TryGetValue(inner, out var negatedComparison) && negatedComparison.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual)
        {
            negated = true;
            definition = negatedComparison;
        }

        if (definition is not { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, var left, var right] }
            || !IsGuard(left, definitions) || !IsGuard(right, definitions))
            return false;

        // The failure path must be the one taken exactly when the two guard values differ.
        var trueWhenDifferent = definition.OpCode == OpCode.CheckNotEqual != negated;
        var failsWhenTrue = taken == failure;
        if (failsWhenTrue != trueWhenDifferent)
            return false;

        branch.SetOperand(1, new Immediate(failsWhenTrue ? 0 : 1));
        return true;
    }

    // A load of the guard, or a copy of one (such as the value the prologue saved in the frame).
    private static bool IsGuard(IOperand operand, Dictionary<LocalVariable, Instruction> definitions,
        HashSet<LocalVariable>? merging = null)
    {
        var value = Copied(operand, definitions);

        // A merge of copies of the guard. Values that only circulate between the merges add nothing else.
        if (value is LocalVariable merged && definitions.TryGetValue(merged, out var phi) && phi.OpCode == OpCode.Phi)
            return !(merging ??= []).Add(merged) || phi.Operands.Skip(1).All(source => IsGuard(source, definitions, merging));

        return value is MemoryOperand { Base: { } threadPointer, Index: null, Scale: 0, Addend: GuardOffset }
               && Copied(threadPointer, definitions) is Register { Name: "SYSREG" } or LocalVariable { Register.Name: "SYSREG" };
    }

    private static IOperand Copied(IOperand operand, Dictionary<LocalVariable, Instruction> definitions)
    {
        var seen = new HashSet<LocalVariable>();
        while (operand is LocalVariable local && seen.Add(local) && definitions.TryGetValue(local, out var definition)
               && definition is { OpCode: OpCode.Move, Operands: [_, var source] })
            operand = source;
        return operand;
    }
}
