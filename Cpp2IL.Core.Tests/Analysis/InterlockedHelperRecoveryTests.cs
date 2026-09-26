using System;
using System.Buffers.Binary;
using System.Linq;
using Cpp2IL.Core.Analysis;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterlockedHelperRecoveryTests
{
    private const ulong Start = 0x49654E4;
    private const ulong Barrier = 0x490A384;

    // The runtime's pointer compare-exchange as the game binary contains it.
    private static uint[] Helper()
    {
        var bytes = Convert.FromHexString("FE4FBFA908FC5FC81F0102EBA100005401FC09C889FFFF3529008052030000145F3F03D5"
            + "E9031F2ABF3B03D53F0100715310889A9B93FE97E00313AAFE4FC1A8C0035FD6");
        return Enumerable.Range(0, bytes.Length / 4).Select(i => BinaryPrimitives.ReadUInt32LittleEndian(bytes.AsSpan(i * 4))).ToArray();
    }

    [Test]
    public void RecognizesThePointerCompareExchange()
        => Assert.That(InterlockedHelperRecovery.IsReferenceCompareExchange(Helper(), Start, target => target == Barrier), Is.True);

    [Test]
    public void RequiresTheWriteBarrier()
        => Assert.That(InterlockedHelperRecovery.IsReferenceCompareExchange(Helper(), Start, _ => false), Is.False);

    [TestCase(2, 0xEB01011Fu)] // compares with the value instead of the comparand
    [TestCase(4, 0xC809FC02u)] // stores the comparand
    [TestCase(4, 0xC809FC21u)] // stores into [X1]
    [TestCase(5, 0x35FFFFA9u)] // retries from the wrong instruction
    [TestCase(12, 0x9A880053u)] // returns the comparand when the exchange failed
    [TestCase(12, 0x9A881033u)] // returns the value
    [TestCase(14, 0xAA0803E0u)] // returns the loaded register without the success merge
    [TestCase(15, 0xA8C153FEu)] // restores a different register
    public void RejectsBodiesWithOtherSemantics(int index, uint word)
    {
        var words = Helper();
        words[index] = word;
        Assert.That(InterlockedHelperRecovery.IsReferenceCompareExchange(words, Start, target => target == Barrier), Is.False);
    }
}
