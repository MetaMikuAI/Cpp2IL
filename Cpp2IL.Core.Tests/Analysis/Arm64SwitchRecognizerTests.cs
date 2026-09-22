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
}
