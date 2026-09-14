using System;
using System.Linq;
using Cpp2IL.Core.Il2CppApiFunctions;
using Disarm;

namespace Cpp2IL.Core.Tests.Isil;

public class Arm64IsInstAnchorTests
{
    private static ulong Find(params uint[] words) => NewArm64KeyFunctionAddresses.FindObjectIsInstTarget(
        Disassembler.Disassemble(words.SelectMany(BitConverter.GetBytes).ToArray(), 0x1000, new Disassembler.Options(true, true, false)).ToList());

    [TestCase(0x14000004u, 0x1010ul)] // B forward
    [TestCase(0x17FFFFFFu, 0x0FFcul)] // B backward
    [TestCase(0x94000004u, 0ul)] // BL is not a tail thunk
    [TestCase(0x54000080u, 0ul)] // conditional branch
    [TestCase(0xD65F03C0u, 0ul)] // RET
    public void OnlyFollowsUnconditionalTailBranches(uint word, ulong expected)
        => Assert.That(NewArm64KeyFunctionAddresses.DecodeBranchThunk(word, 0x1000), Is.EqualTo(expected));

    [Test]
    public void FindsPointerCallImmediatelyBeforeBooleanReturn()
    {
        // bl 0x1100; cmp x0, #0; cset w0, ne; ret
        Assert.That(Find(0x94000040, 0xF100001F, 0x1A9F07E0, 0xD65F03C0), Is.EqualTo(0x1100ul));
    }

    [Test]
    public void DoesNotSelectEarlierMetadataCall()
    {
        Assert.That(Find(0x94000020, 0xAA0003E1, 0x94000040, 0xF100001F, 0x1A9F07E0, 0xD65F03C0), Is.EqualTo(0x1108ul));
    }

    [TestCase(0xF100003Fu, 0x1A9F07E0u)] // cmp x1 instead of pointer return x0
    [TestCase(0xF100001Fu, 0x1A9F17E0u)] // cset eq, not ne
    [TestCase(0xF100041Fu, 0x1A9F07E0u)] // compare against 1, not null
    public void RejectsDifferentReturnTests(uint compare, uint condition)
        => Assert.That(Find(0x94000040, compare, condition, 0xD65F03C0), Is.Zero);

    [Test]
    public void DoesNotReadPastReturn()
        => Assert.That(Find(0xD65F03C0, 0x94000040, 0xF100001F, 0x1A9F07E0), Is.Zero);

    [Test]
    public void RejectsAmbiguousAnchor()
        => Assert.That(Find(0x94000040, 0xF100001F, 0x1A9F07E0, 0x94000050, 0xF100001F, 0x1A9F07E0, 0xD65F03C0), Is.Zero);
}
