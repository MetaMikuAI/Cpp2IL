using System;
using System.Buffers.Binary;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64ImportResolverTests
{
    private static byte[] Thunk() => Convert.FromHexString("100000D0112A43F91042199120021FD6");

    [Test]
    public void ResolvesPageRelativeGotSlot()
    {
        Assert.That(Arm64ImportResolver.ImportSlot(Thunk(), 0x1120), Is.EqualTo(0x3650UL));
        Assert.That(Arm64ImportResolver.ImportSlot(Thunk(), 0x2120), Is.EqualTo(0x4650UL));
    }

    [TestCase(0, 0xD0000000u)] // adrp x0: clobbers an argument
    [TestCase(4, 0xF9432A00u)] // ldr x0, [x16, #0x650]
    [TestCase(8, 0x91194610u)] // mismatched ADD offset
    [TestCase(8, 0x91194200u)] // add x0: clobbers an argument
    [TestCase(8, 0x91594210u)] // shifted ADD does not identify the same GOT slot
    [TestCase(4, 0xF8408611u)] // post-indexed LDR changes the page base
    [TestCase(12, 0xD61F0200u)] // br x16, not the loaded target
    [TestCase(12, 0xD63F0220u)] // blr x17, not a tail jump
    public void RejectsUnprovenThunk(int offset, uint word)
    {
        var bytes = Thunk();
        BinaryPrimitives.WriteUInt32LittleEndian(bytes.AsSpan(offset), word);
        Assert.That(Arm64ImportResolver.ImportSlot(bytes, 0x1120), Is.Null);
    }

    [Test]
    public void RejectsTruncatedEntry() => Assert.That(Arm64ImportResolver.ImportSlot(Thunk().AsSpan(0, 12), 0x1120), Is.Null);

    [TestCase("memcpy", 3)]
    [TestCase("memmove", 3)]
    [TestCase("memset", 3)]
    [TestCase("memcmp", 3)]
    [TestCase("__memcpy_chk", 4)]
    [TestCase("__memmove_chk", 4)]
    [TestCase("__memset_chk", 4)]
    [TestCase("memcpy_custom", null)]
    [TestCase("printf", null)]
    [TestCase(null, null)]
    public void RequiresExactKnownSignature(string? name, int? expected)
        => Assert.That(Arm64ImportResolver.IntegerArgumentCount(name), Is.EqualTo(expected));

    [TestCase("memcpy", "MemCpy")]
    [TestCase("memmove", "MemMove")]
    [TestCase("memset", "MemSet")]
    [TestCase("memcmp", "MemCmp")]
    [TestCase("__memcpy_chk", null)]
    [TestCase(null, null)]
    public void MapsMemoryFunctionsToUnsafeUtility(string? name, string? expected)
        => Assert.That(Arm64ImportResolver.MemoryMethodName(name), Is.EqualTo(expected));
}
