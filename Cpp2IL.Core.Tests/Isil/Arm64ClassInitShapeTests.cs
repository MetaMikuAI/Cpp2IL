using System;
using System.Linq;
using Cpp2IL.Core.Il2CppApiFunctions;
using Disarm;

namespace Cpp2IL.Core.Tests.Isil;

/// <summary>
/// The shape match used to recover Runtime::ClassInit when the export table has been stripped.
/// </summary>
/// <remarks>
/// Both predicates gate whether an address is taken to be a key function, so a wrong encoding
/// mask fails silently: the match just never fires, and every call through the function's thunk
/// comes out as "method not found". Spelling the encodings out here turns that into a test
/// failure instead.
/// </remarks>
public class Arm64ClassInitShapeTests
{
    private static Arm64Instruction Decode(uint word)
        => Disassembler.Disassemble(BitConverter.GetBytes(word), 0x1000, new Disassembler.Options(true, true, false)).ToList()[0];

    [Test]
    public void MatchesTheClassInitEntryTest()
    {
        // LDR W8, [X0,#0xE4] ; CBZ W8, +8 - what Runtime::ClassInit opens with.
        Assert.That(NewArm64KeyFunctionAddresses.IsInitialisedFieldTest(Decode(0xB940E408), Decode(0x34000048)), Is.True);
    }

    [TestCase(0xB940E008u, 0x34000048u, Description = "offset 0xE0, not 0xE4")]
    [TestCase(0xB940E409u, 0x34000048u, Description = "CBZ tests a different register than the load wrote")]
    [TestCase(0xB940E408u, 0x35000048u, Description = "CBNZ - the guard branches the other way")]
    [TestCase(0xF940E408u, 0x34000048u, Description = "64-bit load; the field is 32-bit")]
    [TestCase(0xB941E408u, 0x34000048u, Description = "base is not X0, so this is not the entry test")]
    public void RejectsNearMisses(uint load, uint branch)
        => Assert.That(NewArm64KeyFunctionAddresses.IsInitialisedFieldTest(Decode(load), Decode(branch)), Is.False);

    [TestCase(0xD10083FFu, Description = "SUB SP, SP, #0x20")]
    [TestCase(0xA9BF4FFEu, Description = "STP X30, X19, [SP,#-0x10]!")]
    [TestCase(0xA9BD5FFEu, Description = "STP X30, X23, [SP,#-0x30]!")]
    public void AcceptsPrologues(uint word)
        => Assert.That(NewArm64KeyFunctionAddresses.IsPrologue(Decode(word)), Is.True);

    [TestCase(0xA9014FFEu, Description = "STP at a positive SP offset - mid-function spill, not a prologue")]
    [TestCase(0x910083FFu, Description = "ADD SP, SP, #0x20 - epilogue")]
    [TestCase(0xD65F03C0u, Description = "RET")]
    [TestCase(0xAA0003F3u, Description = "MOV X19, X0")]
    public void RejectsNonPrologues(uint word)
        => Assert.That(NewArm64KeyFunctionAddresses.IsPrologue(Decode(word)), Is.False);
}
