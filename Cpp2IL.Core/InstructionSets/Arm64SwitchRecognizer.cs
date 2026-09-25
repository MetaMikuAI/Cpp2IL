using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.InstructionSets;

internal sealed record Arm64SwitchDispatch(int LoadIndex, int GuardIndex, int Selector, int OffsetRegister,
    int TargetRegister, ulong DefaultTarget, uint[] Offsets, ulong[] Targets, int? ProofStartIndex = null);

// Clang's compact unsigned byte/halfword jump table, guarded by an unsigned W
// comparison. Keep the original guard and preserve the dispatch scratch values.
internal static class Arm64SwitchRecognizer
{
    internal static Dictionary<int, Arm64SwitchDispatch> Find(MethodAnalysisContext context, IReadOnlyList<Arm64Instruction> instructions)
    {
        var result = new Dictionary<int, Arm64SwitchDispatch>();
        if (instructions.Count < 9 || !instructions.Any(i => i.Mnemonic == Arm64Mnemonic.BR)) return result;
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
        for (var i = 6; i + 2 < words.Length; i++)
            if (Decode(words, instructions[0].Address, i, ReadTable) is { } dispatch)
                result.Add(i, dispatch);
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

    internal static Arm64SwitchDispatch? Decode(uint[] words, ulong start, int loadIndex, Func<ulong, int, byte[]?> readTable)
    {
        if (loadIndex < 6 || loadIndex + 2 >= words.Length) return null;
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
        // The table address is either computed right here (ADRP; [MOV;] ADD; ADR) or, in loops, hoisted
        // into a callee-saved register earlier in the method (just [MOV;] ADR).
        var local = (tableAdd & 0xFFC00000) == 0x91000000 && (tableAdd & 31) == table && ((tableAdd >> 5) & 31) == table;
        var copy = words[loadIndex - (local ? 3 : 2)];
        var copiedSelector = (copy & 0xFFE0FFE0) == 0x2A0003E0 && (copy & 31) == selector; // MOV Wd,Wm
        var comparedRegister = copiedSelector ? (int)((copy >> 16) & 31) : selector;
        // ADRP executes before the copy, so it must not overwrite the compared value.
        if (copiedSelector && (comparedRegister == table || comparedRegister == 31)) return null;
        int pageIndex;
        ulong tableAddress;
        if (local)
        {
            pageIndex = loadIndex - (copiedSelector ? 4 : 3);
            var page = words[pageIndex];
            if ((page & 0x9F000000) != 0x90000000 || (page & 31) != table) return null;
            tableAddress = PageAddress(start, pageIndex, page, tableAdd);
        }
        else
        {
            if (HoistedTableAddress(words, start, table, loadIndex) is not { } hoisted) return null;
            pageIndex = loadIndex - (copiedSelector ? 2 : 1);
            tableAddress = hoisted;
        }
        var targetBase = unchecked((ulong)((long)start + (loadIndex - 1) * 4 + AdrImmediate(label)));

        // Permit only independent plain loads between the guard and table setup.
        var guardIndex = pageIndex - 1;
        var minimumGuard = copiedSelector ? 1 : 2;
        while (guardIndex >= minimumGuard && loadIndex - guardIndex <= 8 && IsPlainLoad(words[guardIndex])
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
            // Independent loads may be scheduled between the W definition and CMP.
            // Stop at any other instruction or selector write; do not cross calls or branches.
            while (proofStartIndex > 0 && guardIndex - proofStartIndex < 8
                && IsPlainLoad(words[proofStartIndex]) && (words[proofStartIndex] & 31) != selector)
                proofStartIndex--;
            var definition = words[proofStartIndex];
            if ((definition & 31) != selector || (definition & 0xFFC00000) != 0xB9400000
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

    private static ulong PageAddress(ulong start, int pageIndex, uint page, uint add)
        => unchecked((ulong)((long)((start + (ulong)pageIndex * 4) & ~0xFFFUL) + (AdrImmediate(page) << 12) + ((add >> 10) & 0xFFF)));

    // A callee-saved table register that the whole method writes only with ADRP Xt then ADD Xt,Xt,#imm,
    // both before the table load, holds that address wherever the load runs. Anything that might write
    // the register counts as a write: every word except stores and branches naming it as Rd/Rt, the
    // second register of a load pair, and the base of any other load or store (writeback). Restoring it
    // in an epilogue is not: nothing but the return follows.
    internal static ulong? HoistedTableAddress(uint[] words, ulong start, int table, int loadIndex)
    {
        if (table is < 19 or > 28) return null;
        int page = -1, add = -1;
        for (var i = 0; i < words.Length; i++)
        {
            if (i == loadIndex) continue;
            var word = words[i];
            var loadStore = (word & 0x0A000000) == 0x08000000;
            var branch = (word & 0x1C000000) == 0x14000000;
            var writes = loadStore
                ? ((word >> 5) & 31) == table
                  || (word & (1u << 22)) != 0 && ((word & 31) == table || (word & 0x3A000000) == 0x28000000 && ((word >> 10) & 31) == table)
                : !branch && (word & 31) == table;
            if (!writes || IsEpilogueRestore(words, i)) continue;
            if ((word & 0x9F000000) == 0x90000000 && page < 0) page = i;
            else if ((word & 0xFFC00000) == 0x91000000 && ((word >> 5) & 31) == table && add < 0) add = i;
            else return null;
        }
        return page >= 0 && page < add && add < loadIndex ? PageAddress(start, page, words[page], words[add]) : null;
    }

    // A load from [SP] followed only by further stack loads/stores, ADD SP and hints up to a RET, B or BR.
    private static bool IsEpilogueRestore(uint[] words, int index)
    {
        static bool FromStack(uint word) => (word & 0x0A000000) == 0x08000000 && ((word >> 5) & 31) == 31;
        if (!FromStack(words[index]) || (words[index] & (1u << 22)) == 0) return false;
        for (var i = index + 1; i < words.Length && i <= index + 6; i++)
        {
            var word = words[i];
            if ((word & 0xFFFFFC1F) is 0xD65F0000 or 0xD61F0000 || (word & 0xFC000000) == 0x14000000) return true; // RET / BR / B
            if (!FromStack(word) && (word & 0xFF8003FF) != 0x910003FF && (word & 0xFFFFF01F) != 0xD503201F) return false; // ADD SP / HINT
        }
        return false;
    }

    private static bool IsPlainLoad(uint word) => (word & 0xFFC00000) is 0xF9400000 or 0xB9400000;
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
