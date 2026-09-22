using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.InstructionSets;

internal sealed record Arm64SwitchDispatch(int LoadIndex, int GuardIndex, int Selector, int OffsetRegister,
    int TargetRegister, ulong DefaultTarget, uint[] Offsets, ulong[] Targets);

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
        var page = words[loadIndex - 3];
        var tableAdd = words[loadIndex - 2];
        var label = words[loadIndex - 1];
        if ((page & 0x9F000000) != 0x90000000 || (page & 31) != table
            || (tableAdd & 0xFFC00000) != 0x91000000 || (tableAdd & 31) != table || ((tableAdd >> 5) & 31) != table
            || (label & 0x9F000000) != 0x10000000 || (label & 31) != targetReg) return null;
        var tableAddress = unchecked((ulong)((long)((start + (ulong)(loadIndex - 3) * 4) & ~0xFFFUL)
            + (AdrImmediate(page) << 12) + ((tableAdd >> 10) & 0xFFF)));
        var targetBase = unchecked((ulong)((long)start + (loadIndex - 1) * 4 + AdrImmediate(label)));

        // Permit only independent plain loads between the guard and table setup.
        var guardIndex = loadIndex - 4;
        while (guardIndex >= 2 && loadIndex - guardIndex <= 8 && IsPlainLoad(words[guardIndex])
            && (words[guardIndex] & 31) != selector) guardIndex--;
        if (guardIndex < 2 || loadIndex - guardIndex > 8) return null;
        var guard = words[guardIndex];
        var condition = guard & 15;
        if ((guard & 0xFF000010) != 0x54000000 || condition is not (8 or 2)) return null; // HI / HS
        var compare = words[guardIndex - 1];
        if ((compare & 0xFFC0001F) != 0x7100001F || ((compare >> 5) & 31) != selector) return null;
        // The X-index form requires proven zero upper bits, not just a W compare.
        var definition = words[guardIndex - 2];
        if ((definition & 0xFFC00000) != 0xB9400000 || (definition & 31) != selector) return null;
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
        var candidate = new Arm64SwitchDispatch(loadIndex, guardIndex, selector, offsetReg, targetReg, defaultTarget, offsets, targets);
        if (targets.Append(defaultTarget).Any(t => t < start || (t - start) % 4 != 0 || (t - start) / 4 >= (ulong)words.Length
            || InsideGuard(t, candidate, start))) return null;
        for (var i = 0; i < words.Length; i++)
        {
            if (DirectTarget(words[i], start + (ulong)i * 4) is { } target && InsideGuard(target, candidate, start)) return null;
        }
        return candidate;
    }

    private static bool IsPlainLoad(uint word) => (word & 0xFFC00000) is 0xF9400000 or 0xB9400000;
    private static int ConditionalOffset(uint word) => (int)((word & 0x00FFFFE0) << 8) >> 11;
    private static long AdrImmediate(uint word) => (int)((((word >> 5) & 0x7FFFF) << 2 | (word >> 29) & 3) << 11) >> 11;
    private static bool InsideGuard(ulong target, Arm64SwitchDispatch dispatch, ulong start)
        => target > start + (ulong)(dispatch.GuardIndex - 2) * 4 && target <= start + (ulong)(dispatch.LoadIndex + 2) * 4;
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
