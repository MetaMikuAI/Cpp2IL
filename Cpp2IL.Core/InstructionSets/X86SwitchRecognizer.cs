using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Model.Contexts;
using Iced.Intel;

namespace Cpp2IL.Core.InstructionSets;

internal sealed record X86SwitchDispatch(int StartIndex, int EndIndex, Register Selector, int SelectorSize,
    ulong DefaultTarget, ulong[] CaseTargets);

internal static class X86SwitchRecognizer
{
    public static Dictionary<int, X86SwitchDispatch> Find(MethodAnalysisContext context, IReadOnlyList<Instruction> instructions)
    {
        var result = new Dictionary<int, X86SwitchDispatch>();
        var infoFactory = new InstructionInfoFactory();

        for (var i = 0; i < instructions.Count; i++)
        {
            if (!TryJumpTable(context, instructions, i, infoFactory, out var dispatch)
                && !TryComparisonCascade(instructions, i, infoFactory, out dispatch))
                continue;

            if (!HasSingleEntry(instructions, dispatch)
                || !SelectorComesFromArgument(instructions, dispatch.StartIndex, dispatch.Selector, infoFactory))
                continue;

            result.Add(dispatch.StartIndex, dispatch);
            i = dispatch.EndIndex;
        }

        return result;
    }

    private static bool TryComparisonCascade(IReadOnlyList<Instruction> instructions, int start,
        InstructionInfoFactory infoFactory,
        out X86SwitchDispatch dispatch)
    {
        dispatch = null!;
        if (start + 4 >= instructions.Count)
            return false;

        var cursor = start;
        Register selector;
        Register scratch;
        var cases = new Dictionary<int, ulong>();

        if (TryMoveAndZeroCase(instructions, cursor, out selector, out scratch, out var zeroTarget))
        {
            cases[0] = zeroTarget;
            cursor += 3;
        }
        else if (TryZeroCase(instructions, cursor, out selector, out zeroTarget))
        {
            scratch = selector;
            cases[0] = zeroTarget;
            cursor += 2;
        }
        else if (IsSubtractOne(instructions[cursor], out scratch))
        {
            selector = scratch;
        }
        else
        {
            return false;
        }

        var subtractions = 0;
        while (cursor + 1 < instructions.Count
               && IsSubtractOne(instructions[cursor], out var current)
               && SameRegister(current, scratch)
               && instructions[cursor + 1].Mnemonic == Mnemonic.Je)
        {
            subtractions++;
            cases[subtractions] = instructions[cursor + 1].NearBranchTarget;
            cursor += 2;
        }

        if (subtractions < 2 || cursor + 1 >= instructions.Count
            || !IsRegisterImmediateCompare(instructions[cursor], scratch, out var compared)
            || compared <= 0 || compared > 256)
            return false;

        var terminalBranch = instructions[cursor + 1];
        var terminalCase = checked(subtractions + (int)compared);
        ulong defaultTarget;

        if (terminalBranch.Mnemonic == Mnemonic.Jne)
        {
            cases[terminalCase] = terminalBranch.NextIP;
            defaultTarget = terminalBranch.NearBranchTarget;
        }
        else if (terminalBranch.Mnemonic == Mnemonic.Je)
        {
            cases[terminalCase] = terminalBranch.NearBranchTarget;
            defaultTarget = terminalBranch.NextIP;
        }
        else
        {
            return false;
        }

        var maxCase = cases.Keys.Max();
        if (cases.Count < 3 || maxCase > 256)
            return false;

        var caseTargets = Enumerable.Repeat(defaultTarget, maxCase + 1).ToArray();
        foreach (var pair in cases)
            caseTargets[pair.Key] = pair.Value;

        var candidate = new X86SwitchDispatch(start, cursor + 1, selector, selector.GetSize(), defaultTarget, caseTargets);
        if (!TargetsAreValid(instructions, candidate)
            || !RegisterIsDeadAtTargets(instructions, scratch, caseTargets.Append(defaultTarget), infoFactory))
            return false;

        dispatch = candidate;
        return true;
    }

    private static bool TryJumpTable(MethodAnalysisContext context, IReadOnlyList<Instruction> instructions,
        int start, InstructionInfoFactory infoFactory, out X86SwitchDispatch dispatch)
    {
        dispatch = null!;
        var guardIndex = start;
        var caseOffset = 0;
        Register selector;
        Register tableSelector;
        if (TrySubtractOffset(instructions[start], out selector, out tableSelector, out caseOffset))
            guardIndex++;
        else
            selector = tableSelector = Register.None;

        if (guardIndex + 5 >= instructions.Count)
            return false;

        var compare = instructions[guardIndex];
        var guard = instructions[guardIndex + 1];
        if (!IsRegisterImmediateCompare(compare, out var comparedSelector, out var bound)
            || tableSelector != Register.None && !SameRegister(tableSelector, comparedSelector)
            || bound < 0 || bound >= 4096
            || guard.Mnemonic is not (Mnemonic.Ja or Mnemonic.Jae))
            return false;

        if (selector == Register.None)
            selector = tableSelector = comparedSelector;

        var caseCount = guard.Mnemonic == Mnemonic.Ja ? (int)bound + 1 : (int)bound;
        if (caseCount < 3 || caseOffset + caseCount > 4096)
            return false;

        var loadIndex = guardIndex + 2;
        var imageBase = context.UnderlyingPointer - context.AppContext.Binary.GetRva(context.UnderlyingPointer);
        var sawImageBase = false;
        var imageBaseRegister = Register.None;

        while (loadIndex < instructions.Count)
        {
            var setup = instructions[loadIndex];
            if (!sawImageBase && IsImageBaseLoad(setup, imageBase, out imageBaseRegister))
            {
                sawImageBase = true;
                loadIndex++;
                continue;
            }

            if (setup.Mnemonic == Mnemonic.Cdqe && tableSelector.GetFullRegister() == Register.RAX)
            {
                loadIndex++;
                continue;
            }

            break;
        }

        if (!sawImageBase || loadIndex + 2 >= instructions.Count)
            return false;

        var load = instructions[loadIndex];
        var addressCalculation = instructions[loadIndex + 1];
        var jump = instructions[loadIndex + 2];

        if (jump.Mnemonic != Mnemonic.Jmp || jump.Op0Kind != OpKind.Register
            || load.Mnemonic is not (Mnemonic.Mov or Mnemonic.Movsxd)
            || load.Op0Kind != OpKind.Register || load.Op1Kind != OpKind.Memory
            || !SameRegister(jump.Op0Register, load.Op0Register)
            || !SameRegister(tableSelector, load.MemoryIndex)
            || !SameRegister(load.MemoryBase, imageBaseRegister)
            || load.MemoryIndexScale != 4 || load.MemorySize.GetSize() != 4
            || !AddsImageBase(addressCalculation, jump.Op0Register, load.MemoryBase))
            return false;

        var tableAddress = imageBase + unchecked((uint)load.MemoryDisplacement64);
        var binary = context.AppContext.Binary;
        if (tableAddress != context.UnderlyingPointer + (ulong)context.RawBytes.Length
            || !binary.TryMapVirtualAddressToRaw(tableAddress, out var rawOffset))
            return false;

        var raw = binary.GetRawBinaryContent();
        if (rawOffset + caseCount * 4 > raw.Length)
            return false;

        var targets = Enumerable.Repeat(guard.NearBranchTarget, caseOffset + caseCount).ToArray();
        for (var i = 0; i < caseCount; i++)
            targets[caseOffset + i] = imageBase + raw.ReadUInt((int)rawOffset + i * 4);

        var candidate = new X86SwitchDispatch(start, loadIndex + 2, selector, tableSelector.GetSize(),
            guard.NearBranchTarget, targets);
        if (!TargetsAreValid(instructions, candidate)
            || !RegisterIsDeadAtTargets(instructions, jump.Op0Register, targets, infoFactory)
            || !RegisterIsDeadAtTargets(instructions, load.MemoryBase, targets, infoFactory)
            || caseOffset != 0 && !RegisterIsDeadAtTargets(instructions, tableSelector, targets, infoFactory))
            return false;

        dispatch = candidate;
        return true;
    }

    private static bool TrySubtractOffset(Instruction instruction, out Register selector,
        out Register adjustedSelector, out int offset)
    {
        selector = adjustedSelector = Register.None;
        offset = 0;
        if (instruction.Mnemonic != Mnemonic.Lea || instruction.Op0Kind != OpKind.Register
            || instruction.Op1Kind != OpKind.Memory || instruction.MemoryBase == Register.None
            || instruction.MemoryIndex != Register.None)
            return false;

        var displacement = instruction.MemoryDisplSize switch
        {
            1 => unchecked((sbyte)instruction.MemoryDisplacement64),
            2 => unchecked((short)instruction.MemoryDisplacement64),
            4 => unchecked((int)instruction.MemoryDisplacement64),
            8 => unchecked((long)instruction.MemoryDisplacement64),
            _ => 0
        };
        if (displacement >= 0 || displacement < -256)
            return false;

        selector = instruction.MemoryBase;
        adjustedSelector = instruction.Op0Register;
        offset = (int)-displacement;
        return true;
    }

    private static bool TryMoveAndZeroCase(IReadOnlyList<Instruction> instructions, int index,
        out Register selector, out Register scratch, out ulong target)
    {
        selector = scratch = Register.None;
        target = 0;
        if (index + 2 >= instructions.Count)
            return false;

        var move = instructions[index];
        if (move.Mnemonic != Mnemonic.Mov || move.Op0Kind != OpKind.Register || move.Op1Kind != OpKind.Register
            || !TryZeroCase(instructions, index + 1, out var tested, out target)
            || !SameRegister(move.Op1Register, tested))
            return false;

        selector = move.Op1Register;
        scratch = move.Op0Register;
        return true;
    }

    private static bool TryZeroCase(IReadOnlyList<Instruction> instructions, int index,
        out Register selector, out ulong target)
    {
        selector = Register.None;
        target = 0;
        if (index + 1 >= instructions.Count)
            return false;

        var test = instructions[index];
        var branch = instructions[index + 1];
        if (test.Mnemonic != Mnemonic.Test || test.Op0Kind != OpKind.Register || test.Op1Kind != OpKind.Register
            || !SameRegister(test.Op0Register, test.Op1Register) || branch.Mnemonic != Mnemonic.Je)
            return false;

        selector = test.Op0Register;
        target = branch.NearBranchTarget;
        return true;
    }

    private static bool IsSubtractOne(Instruction instruction, out Register register)
    {
        register = Register.None;
        if (instruction.Mnemonic != Mnemonic.Sub || instruction.Op0Kind != OpKind.Register
            || !IsImmediate(instruction.Op1Kind) || instruction.GetImmediate(1) != 1)
            return false;

        register = instruction.Op0Register;
        return true;
    }

    private static bool IsRegisterImmediateCompare(Instruction instruction, Register expected, out long value)
        => IsRegisterImmediateCompare(instruction, out var actual, out value) && SameRegister(actual, expected);

    private static bool IsRegisterImmediateCompare(Instruction instruction, out Register register, out long value)
    {
        register = Register.None;
        value = 0;
        if (instruction.Mnemonic != Mnemonic.Cmp || instruction.Op0Kind != OpKind.Register
            || !IsImmediate(instruction.Op1Kind))
            return false;

        register = instruction.Op0Register;
        value = unchecked((long)instruction.GetImmediate(1));
        return true;
    }

    private static bool IsImageBaseLoad(Instruction instruction, ulong imageBase, out Register register)
    {
        register = Register.None;
        if (instruction.Mnemonic != Mnemonic.Lea || instruction.Op0Kind != OpKind.Register
            || instruction.Op1Kind != OpKind.Memory || !instruction.IsIPRelativeMemoryOperand
            || instruction.IPRelativeMemoryAddress != imageBase)
            return false;

        register = instruction.Op0Register;
        return true;
    }

    private static bool AddsImageBase(Instruction instruction, Register target, Register imageBase)
    {
        if (instruction.Mnemonic == Mnemonic.Add)
            return instruction.Op0Kind == OpKind.Register && SameRegister(instruction.Op0Register, target)
                && instruction.Op1Kind == OpKind.Register && SameRegister(instruction.Op1Register, imageBase);

        return instruction.Mnemonic == Mnemonic.Lea
            && instruction.Op0Kind == OpKind.Register && SameRegister(instruction.Op0Register, target)
            && instruction.Op1Kind == OpKind.Memory && instruction.MemoryDisplacement64 == 0
            && instruction.MemoryIndexScale == 1
            && (SameRegister(instruction.MemoryBase, target) && SameRegister(instruction.MemoryIndex, imageBase)
                || SameRegister(instruction.MemoryBase, imageBase) && SameRegister(instruction.MemoryIndex, target));
    }

    private static bool TargetsAreValid(IReadOnlyList<Instruction> instructions, X86SwitchDispatch dispatch)
    {
        var addresses = new HashSet<ulong>(instructions.Select(instruction => instruction.IP));
        return dispatch.CaseTargets.Append(dispatch.DefaultTarget).All(target => addresses.Contains(target)
            && (target < instructions[dispatch.StartIndex].IP || target >= instructions[dispatch.EndIndex].NextIP));
    }

    private static bool HasSingleEntry(IReadOnlyList<Instruction> instructions, X86SwitchDispatch dispatch)
    {
        var first = instructions[dispatch.StartIndex].IP;
        var consumed = new HashSet<ulong>(instructions.Skip(dispatch.StartIndex)
            .Take(dispatch.EndIndex - dispatch.StartIndex + 1)
            .Select(instruction => instruction.IP));

        for (var i = 0; i < instructions.Count; i++)
        {
            if (i >= dispatch.StartIndex && i <= dispatch.EndIndex)
                continue;

            var instruction = instructions[i];
            if (instruction.FlowControl is FlowControl.ConditionalBranch or FlowControl.UnconditionalBranch
                && consumed.Contains(instruction.NearBranchTarget) && instruction.NearBranchTarget != first)
                return false;
        }

        return true;
    }

    private static bool RegisterIsDeadAtTargets(IReadOnlyList<Instruction> instructions, Register register,
        IEnumerable<ulong> targets, InstructionInfoFactory infoFactory)
    {
        var indices = instructions.Select((instruction, index) => (instruction.IP, index))
            .ToDictionary(pair => pair.IP, pair => pair.index);
        var pending = new Stack<int>(targets.Distinct().Select(target => indices[target]));
        var visited = new HashSet<int>();
        var fullRegister = register.GetFullRegister();

        while (pending.Count > 0)
        {
            var index = pending.Pop();
            while (index < instructions.Count && visited.Add(index))
            {
                var instruction = instructions[index];
                var used = infoFactory.GetInfo(instruction).GetUsedRegisters()
                    .Where(usedRegister => usedRegister.Register.GetFullRegister() == fullRegister)
                    .ToList();

                if (used.Any(usedRegister => usedRegister.Access is OpAccess.Read or OpAccess.CondRead
                        or OpAccess.ReadWrite or OpAccess.ReadCondWrite))
                    return false;

                if (used.Any(usedRegister => usedRegister.Access is OpAccess.Write or OpAccess.CondWrite
                        && usedRegister.Register.GetSize() >= 4))
                    break;

                if (instruction.FlowControl == FlowControl.ConditionalBranch)
                {
                    if (!indices.TryGetValue(instruction.NearBranchTarget, out var branchTarget))
                        return false;
                    pending.Push(branchTarget);
                }
                else if (instruction.FlowControl == FlowControl.UnconditionalBranch)
                {
                    if (!indices.TryGetValue(instruction.NearBranchTarget, out index))
                        return false;
                    continue;
                }
                else if (instruction.FlowControl is FlowControl.IndirectBranch or FlowControl.Return
                         or FlowControl.Interrupt or FlowControl.Exception)
                {
                    break;
                }

                index++;
            }
        }

        return true;
    }

    private static bool SelectorComesFromArgument(IReadOnlyList<Instruction> instructions, int start, Register selector,
        InstructionInfoFactory infoFactory)
    {
        var indices = instructions.Select((instruction, index) => (instruction.IP, index))
            .ToDictionary(pair => pair.IP, pair => pair.index);
        var predecessors = Enumerable.Range(0, instructions.Count).Select(_ => new List<int>()).ToArray();

        for (var i = 0; i < instructions.Count; i++)
        {
            var instruction = instructions[i];
            if (instruction.FlowControl is FlowControl.ConditionalBranch or FlowControl.UnconditionalBranch
                && indices.TryGetValue(instruction.NearBranchTarget, out var target))
                predecessors[target].Add(i);

            if (i + 1 < instructions.Count && instruction.FlowControl is FlowControl.Next
                    or FlowControl.Call or FlowControl.IndirectCall or FlowControl.ConditionalBranch)
                predecessors[i + 1].Add(i);
        }

        var pending = new Stack<(int Index, Register Tracked)>();
        pending.Push((start, selector.GetFullRegister()));
        var visited = new HashSet<(int, Register)>();
        var reachedEntry = false;

        while (pending.Count > 0)
        {
            var (index, tracked) = pending.Pop();
            if (!visited.Add((index, tracked)))
                continue;
            if (visited.Count > 4096)
                return false;

            if (predecessors[index].Count == 0)
            {
                if (index != 0 || !IsArgumentRegister(tracked))
                    return false;
                reachedEntry = true;
                continue;
            }

            foreach (var predecessor in predecessors[index])
            {
                if (predecessor >= start)
                    return false;

                var instruction = instructions[predecessor];
                if (instruction.FlowControl is FlowControl.Call or FlowControl.IndirectCall && IsVolatile(tracked))
                    return false;

                var source = tracked;
                var writesTracked = infoFactory.GetInfo(instruction).GetUsedRegisters().Any(usedRegister =>
                    usedRegister.Register.GetFullRegister() == tracked
                    && usedRegister.Access is OpAccess.Write or OpAccess.CondWrite
                        or OpAccess.ReadWrite or OpAccess.ReadCondWrite);
                if (writesTracked && !IsRegisterCopy(instruction, tracked, out source))
                    return false;

                pending.Push((predecessor, source));
            }
        }

        return reachedEntry;
    }

    private static bool IsArgumentRegister(Register register)
        => register is Register.RCX or Register.RDX or Register.R8 or Register.R9;

    private static bool IsRegisterCopy(Instruction instruction, Register destination, out Register source)
    {
        source = Register.None;
        if (instruction.Mnemonic is not (Mnemonic.Mov or Mnemonic.Movsx or Mnemonic.Movsxd or Mnemonic.Movzx)
            || instruction.Op0Kind != OpKind.Register || instruction.Op1Kind != OpKind.Register
            || instruction.Op0Register.GetFullRegister() != destination)
            return false;

        source = instruction.Op1Register.GetFullRegister();
        return true;
    }

    private static bool IsVolatile(Register register)
        => register is Register.RAX or Register.RCX or Register.RDX or Register.R8 or Register.R9
            or Register.R10 or Register.R11;

    private static bool SameRegister(Register left, Register right)
        => left != Register.None && right != Register.None && left.GetFullRegister() == right.GetFullRegister();

    private static bool IsImmediate(OpKind kind) => kind is OpKind.Immediate8 or OpKind.Immediate8_2nd
        or OpKind.Immediate16 or OpKind.Immediate32 or OpKind.Immediate64 or OpKind.Immediate8to16
        or OpKind.Immediate8to32 or OpKind.Immediate8to64 or OpKind.Immediate32to64;
}
