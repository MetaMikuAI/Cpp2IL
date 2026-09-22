using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.InstructionSets;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64SwitchRecognizerTests
{
    private const ulong Start = 0x525A378;

    [Test]
    public void RejectedTableEdgesStillParticipateInGuardProof()
    {
        var candidates = new Dictionary<int, Arm64SwitchDispatch>
        {
            [6] = new(6, 2, 8, 11, 10, 0x2000, [0], [0x1030]),
            [16] = new(16, 12, 8, 11, 10, 0x2000, [0], [0x1010])
        };
        Arm64SwitchRecognizer.RemoveGuardBypasses(candidates, 0x1000);
        Assert.That(candidates, Is.Empty);
    }
    private static uint[] Fixture()
    {
        // Captured dispatch; unrelated case bodies are RETs to keep the fixture small.
        var words = Enumerable.Repeat(0xD65F03C0u, 202).ToArray();
        var prefix = Convert.FromHexString("681240B91F0D0071E8180054741240F9E963FEB0296112918A0000102B6968384A090B8B40011FD6");
        for (var i = 0; i < prefix.Length / 4; i++) words[i] = BinaryPrimitives.ReadUInt32LittleEndian(prefix.AsSpan(i * 4));
        return words;
    }

    private static uint[] CopiedSelectorFixture()
    {
        var words = Fixture();
        words[0] = 0xD503201F; // No definition of W20 needed before CMP.
        words[1] = 0x71000E9F; // CMP W20,#3
        words[3] = words[4]; // ADRP X9 before the copy
        words[4] = 0x2A1403E8; // MOV W8,W20
        return words;
    }

    [TestCase(false)] [TestCase(true)]
    public void CopiedSelectorProvesBoundsAndUpperBits(bool halfword)
    {
        var words = CopiedSelectorFixture();
        if (halfword) words[7] = 0x7868792B;
        // ADRP is the last instruction on this page; MOV starts the next page.
        const ulong start = 0x525AFF0;
        var result = Arm64SwitchRecognizer.Decode(words, start, 7, (address, length) =>
        {
            Assert.That(address, Is.EqualTo(0x1ED7498UL));
            Assert.That(length, Is.EqualTo(halfword ? 8 : 4));
            return halfword ? [0, 0, 41, 0, 86, 0, 97, 0] : [0, 41, 86, 97];
        });
        Assert.That(result, Is.Not.Null);
        Assert.That(result!.Selector, Is.EqualTo(8));
        Assert.That(result.ProofStartIndex, Is.EqualTo(1));
        Assert.That(result.Targets, Is.EqualTo(new ulong[] { start + 40, start + 204, start + 384, start + 428 }));
    }

    [TestCase("wrongSource")] [TestCase("wideCopy")] [TestCase("wrongDestination")]
    [TestCase("tableOverwritesSource")] [TestCase("entryAtCopy")]
    [TestCase("entryAtGuard")] [TestCase("entryAtTable")]
    public void RejectsUnprovenSelectorCopies(string shape)
    {
        var words = CopiedSelectorFixture();
        switch (shape)
        {
            case "wrongSource": words[4] = 0x2A1503E8; break; // MOV W8,W21
            case "wideCopy": words[4] = 0xAA1403E8; break; // MOV X8,X20
            case "wrongDestination": words[4] = 0x2A1403EC; break;
            case "tableOverwritesSource":
                words[1] = 0x71000D3F; // CMP W9,#3
                words[4] = 0x2A0903E8; // MOV W8,W9 after ADRP X9
                break;
            case "entryAtCopy": words[12] = 0x17FFFFF8; break;
            case "entryAtGuard": words[12] = 0x17FFFFF6; break;
            case "entryAtTable": words[12] = 0x17FFFFF7; break;
        }
        Assert.That(Arm64SwitchRecognizer.Decode(words, Start, 7, (_, _) => [0, 41, 86, 97]), Is.Null);
    }

    [Test]
    public void CopiedSelectorAllowsEntryAtComparison()
    {
        var words = CopiedSelectorFixture();
        words[12] = 0x17FFFFF5; // Entry at CMP still executes the guard and W copy.
        Assert.That(Arm64SwitchRecognizer.Decode(words, Start, 7, (_, _) => [0, 41, 86, 97]), Is.Not.Null);
    }

    [TestCase(20, false)] [TestCase(21, true)]
    public void LoadsBetweenGuardAndCopyMustPreserveComparedValue(int destination, bool expected)
    {
        var words = CopiedSelectorFixture();
        words[0] = words[1];
        words[1] = words[2] + 0x20; // Guard moved back one instruction; keep target.
        words[2] = 0xB9400260u | (uint)destination; // LDR Wd,[X19]
        Assert.That(Arm64SwitchRecognizer.Decode(words, Start, 7, (_, _) => [0, 41, 86, 97]) != null, Is.EqualTo(expected));
    }

    [TestCase(false)] [TestCase(true)]
    public void DecodesUnsignedCompactTablesAndPreservesScratchResults(bool halfword)
    {
        var words = Fixture();
        if (halfword) words[7] = 0x7868792B; // LDRH W11,[X9,X8,LSL #1]
        var result = Arm64SwitchRecognizer.Decode(words, Start, 7, (address, length) =>
        {
            Assert.That(address, Is.EqualTo(0x1ED7498UL));
            Assert.That(length, Is.EqualTo(halfword ? 8 : 4));
            return halfword ? [0, 0, 41, 0, 86, 0, 97, 0] : [0, 41, 86, 97];
        });
        Assert.That(result, Is.Not.Null);
        Assert.Multiple(() =>
        {
            Assert.That(result!.DefaultTarget, Is.EqualTo(0x525A69CUL));
            Assert.That(result.Targets, Is.EqualTo(new ulong[] { 0x525A3A0, 0x525A444, 0x525A4F8, 0x525A524 }));
            Assert.That(result.Offsets, Is.EqualTo(new uint[] { 0, 41, 86, 97 }));
            Assert.That(result.Selector, Is.EqualTo(8));
            Assert.That(result.OffsetRegister, Is.EqualTo(11));
            Assert.That(result.TargetRegister, Is.EqualTo(10));
        });
    }

    [TestCase("signedGuard")] [TestCase("unknownUpperBits")] [TestCase("changedSelector")]
    [TestCase("unscaledHalfword")] [TestCase("signedTable")] [TestCase("wrongBase")]
    [TestCase("wrongShift")] [TestCase("wrongBranchRegister")] [TestCase("callBeforeTable")]
    [TestCase("entryBypassesGuard")] [TestCase("outsideMethod")] [TestCase("targetInsideDispatch")]
    [TestCase("unreadableTable")] [TestCase("truncatedTable")]
    public void RejectsUnprovenBoundsAddressesAndControlFlow(string shape)
    {
        var words = Fixture();
        byte[]? table = [0, 41, 86, 97];
        switch (shape)
        {
            case "signedGuard": words[2] = (words[2] & ~15u) | 12; break;
            case "unknownUpperBits": words[0] = 0xF9401268; break; // LDR X8 rather than W8
            case "changedSelector": words[3] = 0xB9401288; break;
            case "unscaledHalfword": words[7] = 0x7868692B; break;
            case "signedTable": words[7] = 0x38A8692B; break;
            case "wrongBase": words[5] ^= 1; break;
            case "wrongShift": words[8] ^= 0x400; break;
            case "wrongBranchRegister": words[9] ^= 0x20; break;
            case "callBeforeTable": words[3] = 0x94000001; break;
            case "entryBypassesGuard": words[12] = 0x17FFFFF5; break; // B to CMP
            case "outsideMethod": table = [0, 41, 86, 255]; break;
            case "targetInsideDispatch": words[6] = 0x1000000A; break; // ADR to itself
            case "unreadableTable": table = null; break;
            case "truncatedTable": table = [0, 41]; break;
        }
        Assert.That(Arm64SwitchRecognizer.Decode(words, Start, 7, (_, _) => table), Is.Null);
    }

    [Test]
    public void SupportsUnsignedExclusiveBound()
    {
        var words = Fixture();
        words[1] = 0x7100111F; // CMP W8,#4
        words[2] = (words[2] & ~15u) | 2; // B.HS
        var result = Arm64SwitchRecognizer.Decode(words, Start, 7, (_, length) =>
        {
            Assert.That(length, Is.EqualTo(4));
            return [0, 41, 86, 97];
        });
        Assert.That(result, Is.Not.Null);
    }

    [TestCase(0x51000C08u, true)] // SUB W8,W0,#3
    [TestCase(0x51000908u, true)] // SUB W8,W8,#2
    [TestCase(0x11000C08u, true)] // ADD W8,W0,#3 (negative first case)
    [TestCase(0x51400408u, true)] // SUB W8,W0,#1,LSL #12
    [TestCase(0x11400408u, true)] // ADD W8,W0,#1,LSL #12
    [TestCase(0xD1000C08u, false)] // SUB X8,X0,#3 does not clear upper bits
    [TestCase(0x91000C08u, false)] // ADD X8,X0,#3
    [TestCase(0x51000C09u, false)] // W9 is not the guarded selector
    [TestCase(0x4B000108u, false)] // Register SUB is not the supported immediate shape
    [TestCase(0x51800C08u, false)] // Reserved opcode bit
    public void NormalizedSelectorStillRequiresAProven32BitDefinition(uint definition, bool expected)
    {
        var words = Fixture();
        words[0] = definition;
        var result = Arm64SwitchRecognizer.Decode(words, Start, 7, (_, _) => [0, 41, 86, 97]);
        Assert.That(result != null, Is.EqualTo(expected));
        if (expected)
        {
            Assert.That(result!.Selector, Is.EqualTo(8));
            Assert.That(result.Targets, Is.EqualTo(new ulong[] { 0x525A3A0, 0x525A444, 0x525A4F8, 0x525A524 }));
        }
    }
}
