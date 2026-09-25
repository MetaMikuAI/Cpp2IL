using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.InstructionSets;

internal sealed record Arm64SwitchDispatch(int LoadIndex, int GuardIndex, int Selector, int OffsetRegister,
    int TargetRegister, ulong DefaultTarget, uint[] Offsets, ulong[] Targets, int? ProofStartIndex = null, bool HoistedTable = false);

// Clang's compact unsigned byte/halfword jump table, guarded by an unsigned W
// comparison. Keep the original guard and preserve the dispatch scratch values.
// The table base is either materialized right before the dispatch or, when the
// compiler hoisted it out of a loop, held in a register the method never repoints.
internal static class Arm64SwitchRecognizer
{
    internal static Dictionary<int, Arm64SwitchDispatch> Find(MethodAnalysisContext context, IReadOnlyList<Arm64Instruction> instructions)
    {
        var result = new Dictionary<int, Arm64SwitchDispatch>();
        if (instructions.Count < 7 || !instructions.Any(i => i.Mnemonic == Arm64Mnemonic.BR)) return result;
        var binary = context.AppContext.Binary;
        if (!binary.TryMapVirtualAddressToRaw(instructions[0].Address, out var raw)) return result;
        var bytes = binary.GetRawBinaryContent();
        var binaryLength = bytes.Length;
        var size = instructions.Count * 4;
        if (raw < 0 || raw > bytes.Length - size
            || !binary.TryMapVirtualAddressToRaw(instructions[^1].Address + 3, out var last) || last != raw + size - 1) return result;
        var words = new uint[instructions.Count];
        for (var i = 0; i < words.Length; i++) words[i] = BinaryPrimitives.ReadUInt32LittleEndian(bytes.Slice((int)raw + i * 4, 4));
        byte[]? ReadTable(ulong address, int length)
        {
            if (!binary.TryMapVirtualAddressToRaw(address, out var start) || start < 0 || start > binaryLength - length
                || !binary.TryMapVirtualAddressToRaw(address + (ulong)length - 1, out var end) || end != start + length - 1) return null;
            for (var offset = 0; offset < length; offset++)
                if (!binary.IsVirtualAddressReadOnly(address + (ulong)offset)) return null;
            return binary.GetRawBinaryContent().Slice((int)start, length).ToArray();
        }
        for (var i = 3; i + 2 < words.Length; i++)
            if (Decode(words, instructions[0].Address, i, ReadTable) is { } dispatch)
                result.Add(i, dispatch);
        // A table base hoisted out of the dispatch block is proven over the whole method, with the
        // case entries of every table found so far counted as branch targets.
        var caseTargets = result.Values.SelectMany(d => d.Targets).ToHashSet();
        ulong? InvariantTable(int register, int _) => ProveInvariantTable(instructions, words, register, caseTargets);
        for (var i = 3; i + 2 < words.Length; i++)
            if (!result.ContainsKey(i) && Decode(words, instructions[0].Address, i, ReadTable, InvariantTable) is { } dispatch)
                result.Add(i, dispatch with { HoistedTable = true });
        caseTargets.UnionWith(result.Values.SelectMany(d => d.Targets));
        foreach (var (index, dispatch) in result.ToArray())
            if (dispatch.HoistedTable && ProveInvariantTable(instructions, words, (int)((words[index] >> 5) & 31), caseTargets) == null)
                result.Remove(index);
        RemoveGuardBypasses(result, instructions[0].Address);
        return result;
    }

    internal static void RemoveGuardBypasses(Dictionary<int, Arm64SwitchDispatch> result, ulong start)
    {
        // Even a table we reject still exists in native code. Snapshot all its
        // edges before removing candidates, so filtering order cannot hide one.
        var indirectTargets = result.Values.SelectMany(d => d.Targets.Append(d.DefaultTarget)).ToArray();
        foreach (var (index, dispatch) in result.ToArray())
            if (indirectTargets.Any(target => InsideGuard(target, dispatch, start))) result.Remove(index);
    }

    internal static Arm64SwitchDispatch? Decode(uint[] words, ulong start, int loadIndex, Func<ulong, int, byte[]?> readTable,
        Func<int, int, ulong?>? invariantTable = null)
    {
        if (loadIndex < 3 || loadIndex + 2 >= words.Length) return null;
        var load = words[loadIndex];
        var width = (load & 0xFFE0FC00) switch
        {
            0x38606800 => 1, // LDRB Wt,[Xn,Xm]
            0x78607800 => 2, // LDRH Wt,[Xn,Xm,LSL #1]
            _ => 0
        };
        if (width == 0) return null;
        var selector = (int)((load >> 16) & 31);
        var table = (int)((load >> 5) & 31);
        var offsetReg = (int)(load & 31);
        var add = words[loadIndex + 1];
        var targetReg = (int)(add & 31);
        if ((add & 0xFFE0FC00) != 0x8B000800 // ADD Xd,Xn,Xm,LSL #2
            || ((add >> 5) & 31) != targetReg || ((add >> 16) & 31) != offsetReg
            || (words[loadIndex + 2] & 0xFFFFFC1F) != 0xD61F0000
            || ((words[loadIndex + 2] >> 5) & 31) != targetReg
            || new[] { selector, table, offsetReg, targetReg }.Any(r => r == 31)
            || table == targetReg || offsetReg == targetReg || selector == table || selector == targetReg) return null;
        var label = words[loadIndex - 1];
        if ((label & 0x9F000000) != 0x10000000 || (label & 31) != targetReg) return null;
        var tableAdd = words[loadIndex - 2];
        int pageIndex;
        bool copiedSelector;
        int comparedRegister;
        ulong tableAddress;
        if (loadIndex >= 6 && (tableAdd & 0xFFC00000) == 0x91000000 && (tableAdd & 31) == table && ((tableAdd >> 5) & 31) == table)
        {
            var copy = words[loadIndex - 3];
            copiedSelector = IsSelectorCopy(copy, selector);
            comparedRegister = copiedSelector ? (int)((copy >> 16) & 31) : selector;
            // ADRP executes before the copy, so it must not overwrite the compared value.
            if (copiedSelector && (comparedRegister == table || comparedRegister == 31)) return null;
            pageIndex = loadIndex - (copiedSelector ? 4 : 3);
            var page = words[pageIndex];
            if ((page & 0x9F000000) != 0x90000000 || (page & 31) != table) return null;
            tableAddress = unchecked((ulong)((long)((start + (ulong)pageIndex * 4) & ~0xFFFUL)
                + (AdrImmediate(page) << 12) + ((tableAdd >> 10) & 0xFFF)));
        }
        else
        {
            // The dispatch starts at the ADR; the table register already holds the proven base.
            if (invariantTable?.Invoke(table, loadIndex) is not { } invariant) return null;
            var copy = words[loadIndex - 2];
            copiedSelector = IsSelectorCopy(copy, selector);
            comparedRegister = copiedSelector ? (int)((copy >> 16) & 31) : selector;
            if (copiedSelector && (comparedRegister == table || comparedRegister == 31)) return null;
            pageIndex = loadIndex - (copiedSelector ? 2 : 1);
            tableAddress = invariant;
        }
        var targetBase = unchecked((ulong)((long)start + (loadIndex - 1) * 4 + AdrImmediate(label)));

        // Permit only independent loads, stores and register moves between the guard and table setup.
        var guardIndex = pageIndex - 1;
        var minimumGuard = copiedSelector ? 1 : 2;
        while (guardIndex >= minimumGuard && loadIndex - guardIndex <= 8 && IsIndependent(words[guardIndex])
            && (words[guardIndex] & 31) != selector && (words[guardIndex] & 31) != comparedRegister) guardIndex--;
        if (guardIndex < minimumGuard || loadIndex - guardIndex > 8) return null;
        var guard = words[guardIndex];
        var condition = guard & 15;
        if ((guard & 0xFF000010) != 0x54000000 || condition is not (8 or 2)) return null; // HI / HS
        var compare = words[guardIndex - 1];
        if ((compare & 0xFFC0001F) != 0x7100001F || ((compare >> 5) & 31) != comparedRegister) return null;
        // The X-index form requires proven zero upper bits, not just a W compare.
        // W ADD/SUB also proves this when normalizing a nonzero first case.
        var proofStartIndex = guardIndex - 1;
        if (!copiedSelector)
        {
            proofStartIndex--;
            // Independent loads, stores and moves may be scheduled between the W definition and CMP.
            // Stop at any other instruction or selector write; do not cross calls or branches.
            while (proofStartIndex > 0 && guardIndex - proofStartIndex < 8
                && IsIndependent(words[proofStartIndex]) && (words[proofStartIndex] & 31) != selector)
                proofStartIndex--;
            // LDR/LDRB/LDRH Wt and W ADD/SUB immediate all zero the upper half of the X register.
            var definition = words[proofStartIndex];
            if ((definition & 31) != selector || (definition & 0xFFC00000) is not (0xB9400000 or 0x39400000 or 0x79400000)
                && (definition & 0xFF800000) is not (0x11000000 or 0x51000000)) return null;
        }
        var count = (int)((compare >> 10) & 0xFFF) + (condition == 8 ? 1 : 0);
        if (count is < 2 or > 4096) return null;
        var defaultTarget = unchecked((ulong)((long)start + guardIndex * 4 + ConditionalOffset(guard)));
        var data = readTable(tableAddress, count * width);
        if (data == null || data.Length != count * width) return null;
        var offsets = new uint[count];
        var targets = new ulong[count];
        for (var i = 0; i < count; i++)
        {
            offsets[i] = width == 1 ? data[i] : BinaryPrimitives.ReadUInt16LittleEndian(data.AsSpan(i * 2));
            targets[i] = targetBase + offsets[i] * 4UL;
        }
        var candidate = new Arm64SwitchDispatch(loadIndex, guardIndex, selector, offsetReg, targetReg, defaultTarget, offsets, targets,
            proofStartIndex);
        if (targets.Append(defaultTarget).Any(t => t < start || (t - start) % 4 != 0 || (t - start) / 4 >= (ulong)words.Length
            || InsideGuard(t, candidate, start))) return null;
        for (var i = 0; i < words.Length; i++)
        {
            if (DirectTarget(words[i], start + (ulong)i * 4) is { } target && InsideGuard(target, candidate, start)) return null;
        }
        return candidate;
    }

    private static bool IsSelectorCopy(uint word, int selector) => (word & 0xFFE0FFE0) == 0x2A0003E0 && (word & 31) == selector; // MOV Wd,Wm

    /// <summary>
    /// The address a jump-table register holds wherever the method reads it, when every write to the
    /// register is the same ADRP/ADD materialization of that address or a frame restore on the way
    /// out of the method. The register then carries only the table or the caller's value, and the
    /// compiler never indexes a jump table through the caller's value. Materializations must run
    /// straight through: no branch leaves between the ADRP and its ADD and none lands between them.
    /// A caller-saved register is rejected when the method makes any call, as the call clobbers it.
    /// </summary>
    internal static ulong? ProveInvariantTable(IReadOnlyList<Arm64Instruction> instructions, uint[] words, int register,
        HashSet<ulong>? caseTargets = null)
    {
        if (register is < 0 or > 30 || instructions.Count != words.Length || instructions.Count == 0) return null;
        var start = instructions[0].Address;
        var end = start + (ulong)instructions.Count * 4;
        var targets = caseTargets == null ? new HashSet<ulong>() : new HashSet<ulong>(caseTargets);
        for (var i = 0; i < words.Length; i++)
            if (DirectTarget(words[i], start + (ulong)i * 4) is { } target)
                targets.Add(target);

        ulong? address = null;
        for (var i = 0; i < instructions.Count; i++)
        {
            if (!MayWrite(instructions[i], register)) continue;
            if ((words[i] & 0x9F000000) == 0x90000000 && (words[i] & 31) == register)
            {
                var j = i + 1;
                for (; j < instructions.Count && !MayWrite(instructions[j], register); j++)
                    if (IsBranch(instructions[j]) || targets.Contains(instructions[j].Address)) return null;
                // ADD Xd,Xn,#imm12 without the LSL #12 form, into the same register.
                if (j == instructions.Count || targets.Contains(instructions[j].Address)
                    || (words[j] & 0xFFC00000) != 0x91000000 || (words[j] & 31) != register || ((words[j] >> 5) & 31) != register)
                    return null;
                var value = unchecked((ulong)((long)(instructions[i].Address & ~0xFFFUL) + (AdrImmediate(words[i]) << 12)
                    + ((words[j] >> 10) & 0xFFF)));
                if (address != null && address != value) return null;
                address = value;
                i = j;
                continue;
            }
            if (IsFrameRestore(instructions[i], register) && LeavesMethod(instructions, words, i, start, end)) continue;
            return null;
        }
        return address;
    }

    private static int RegisterNumber(Arm64Register register) => register switch
    {
        >= Arm64Register.X0 and <= Arm64Register.X31 => register - Arm64Register.X0,
        >= Arm64Register.W0 and <= Arm64Register.W31 => register - Arm64Register.W0,
        _ => -1
    };

    private static bool IsBranch(Arm64Instruction insn) => insn.Mnemonic is Arm64Mnemonic.B or Arm64Mnemonic.BL or Arm64Mnemonic.BLR
        or Arm64Mnemonic.BR or Arm64Mnemonic.RET or Arm64Mnemonic.RETAA or Arm64Mnemonic.RETAB or Arm64Mnemonic.CBZ
        or Arm64Mnemonic.CBNZ or Arm64Mnemonic.TBZ or Arm64Mnemonic.TBNZ;

    // Conservative: any form not known to only read its first register operand writes it.
    private static bool MayWrite(Arm64Instruction insn, int register)
    {
        var name = insn.Mnemonic.ToString();
        if (insn.Mnemonic is Arm64Mnemonic.INVALID || name is "UNIMPLEMENTED" || name.StartsWith("CASP", StringComparison.Ordinal))
            return true;
        if (insn.Mnemonic is Arm64Mnemonic.BL or Arm64Mnemonic.BLR)
            return register is <= 18 or 30;
        if (insn.MemIndexMode is Arm64MemoryIndexMode.PreIndex or Arm64MemoryIndexMode.PostIndex && RegisterNumber(insn.MemBase) == register)
            return true;
        if (insn.Op0Kind == Arm64OperandKind.Register && RegisterNumber(insn.Op0Reg) == register && !ReadsFirstOperandOnly(name))
            return true;
        return insn.Op1Kind == Arm64OperandKind.Register && RegisterNumber(insn.Op1Reg) == register && WritesSecondOperand(name);
    }

    // Stores other than the exclusive ones (which report status in the first operand), comparisons and register branches.
    private static bool ReadsFirstOperandOnly(string name) => name.StartsWith("ST", StringComparison.Ordinal)
        ? !name.Contains("XR") && !name.Contains("XP")
        : name is "CMP" or "CMN" or "TST" or "CCMP" or "CCMN" or "CBZ" or "CBNZ" or "TBZ" or "TBNZ" or "BR" or "RET" or "PRFM";

    private static readonly string[] AtomicLoadPrefixes = ["LDADD", "LDCLR", "LDEOR", "LDSET", "LDSMAX", "LDSMIN", "LDUMAX", "LDUMIN", "SWP"];

    private static bool WritesSecondOperand(string name) => name is "LDP" or "LDPSW" or "LDNP" or "LDXP" or "LDAXP"
        || AtomicLoadPrefixes.Any(prefix => name.StartsWith(prefix, StringComparison.Ordinal));

    private static bool IsFrameRestore(Arm64Instruction insn, int register) => insn.Mnemonic is Arm64Mnemonic.LDP or Arm64Mnemonic.LDR
        && insn.MemBase is Arm64Register.X31 or Arm64Register.W31
        && (RegisterNumber(insn.Op0Reg) == register || insn.Mnemonic == Arm64Mnemonic.LDP && RegisterNumber(insn.Op1Reg) == register);

    // From a restore, the method runs straight to a return or a tail branch out of its body. A register
    // branch is a tail call unless it has the jump-table shape (ADD Xd,Xn,Xm,LSL #2 into its register).
    private static bool LeavesMethod(IReadOnlyList<Arm64Instruction> instructions, uint[] words, int restore, ulong start, ulong end)
    {
        for (var i = restore + 1; i < instructions.Count && i <= restore + 16; i++)
        {
            var insn = instructions[i];
            if (insn.Mnemonic is Arm64Mnemonic.RET or Arm64Mnemonic.RETAA or Arm64Mnemonic.RETAB) return true;
            if (insn.Mnemonic == Arm64Mnemonic.B && insn.MnemonicConditionCode is Arm64ConditionCode.NONE or Arm64ConditionCode.AL)
                return insn.BranchTarget < start || insn.BranchTarget >= end;
            if ((words[i] & 0xFFFFFC1F) == 0xD61F0000)
                return (words[i - 1] & 0xFFE0FC00) != 0x8B000800 || (words[i - 1] & 31) != ((words[i] >> 5) & 31);
            if (IsBranch(insn)) return false;
        }
        return false;
    }

    private static bool IsPlainLoad(uint word) => (word & 0xFFC00000) is 0xF9400000 or 0xB9400000;

    // Writes at most its first register operand: a plain load, a register move (ORR with the zero
    // register), or an unsigned-offset store, which writes no register at all.
    private static bool IsIndependent(uint word) => IsPlainLoad(word) || (word & 0x7FE0FFE0) == 0x2A0003E0
        || (word & 0xFFC00000) is 0xF9000000 or 0xB9000000 or 0x79000000 or 0x39000000;
    private static int ConditionalOffset(uint word) => (int)((word & 0x00FFFFE0) << 8) >> 11;
    private static long AdrImmediate(uint word) => (int)((((word >> 5) & 0x7FFFF) << 2 | (word >> 29) & 3) << 11) >> 11;
    private static bool InsideGuard(ulong target, Arm64SwitchDispatch dispatch, ulong start)
        => target > start + (ulong)(dispatch.ProofStartIndex ?? dispatch.GuardIndex - 2) * 4 && target <= start + (ulong)(dispatch.LoadIndex + 2) * 4;
    private static ulong? DirectTarget(uint word, ulong pc)
    {
        long delta;
        if ((word & 0x7C000000) == 0x14000000) delta = (int)(word << 6) >> 4; // B / BL
        else if ((word & 0xFF000010) == 0x54000000 || (word & 0x7E000000) == 0x34000000)
            delta = ConditionalOffset(word); // B.cond / CBZ / CBNZ
        else if ((word & 0x7E000000) == 0x36000000) delta = (int)((word & 0x0007FFE0) << 13) >> 16; // TBZ / TBNZ
        else return null;
        return unchecked((ulong)((long)pc + delta));
    }
}
