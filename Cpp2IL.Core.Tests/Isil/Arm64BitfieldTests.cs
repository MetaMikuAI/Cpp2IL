using Cpp2IL.Core.InstructionSets;

namespace Cpp2IL.Core.Tests.Isil;

public class Arm64BitfieldTests
{
    // BFI/BFXIL/UBFX build their masks from an ARM64 bitfield width, which can legitimately be
    // the full register width. A plain `(1L << width) - 1` silently yields 0 at width 64,
    // because C# masks the shift count to 63 - the resulting mask would drop every bit of the
    // inserted field instead of keeping all of them.
    [Test]
    public void LowBitMaskCoversFullRegisterWidth()
    {
        Assert.That(NewArmV8InstructionSet.LowBitMask(64), Is.EqualTo(-1L));
    }

    [TestCase(0, 0L)]
    [TestCase(1, 0x1L)]
    [TestCase(7, 0x7FL)]
    [TestCase(8, 0xFFL)]
    [TestCase(16, 0xFFFFL)]
    [TestCase(24, 0xFFFFFFL)]
    [TestCase(31, 0x7FFFFFFFL)]
    [TestCase(32, 0xFFFFFFFFL)]
    [TestCase(63, 0x7FFFFFFFFFFFFFFFL)]
    public void LowBitMaskSetsExactlyWidthBits(int width, long expected)
    {
        Assert.That(NewArmV8InstructionSet.LowBitMask(width), Is.EqualTo(expected));
    }

    // The mask a BFI keeps of its destination is the complement of the field it overwrites.
    // These are the shapes actually seen in a shipped arm64 libil2cpp: a LEB128 varint decoder
    // (7-bit fields at successive offsets) and 16/32-bit struct field packing.
    [TestCase(7, 7, unchecked((int)0xFFFFC07F))]
    [TestCase(14, 7, unchecked((int)0xFFE03FFF))]
    [TestCase(21, 7, unchecked((int)0xF01FFFFF))]
    [TestCase(8, 24, 0x000000FF)]
    [TestCase(0, 16, unchecked((int)0xFFFF0000))]
    public void BfiKeepMaskComplementsInsertedField(int lsb, int width, int expected)
    {
        var keepMask = ~(NewArmV8InstructionSet.LowBitMask(width) << lsb) & 0xFFFFFFFFL;

        Assert.That(keepMask, Is.EqualTo((uint)expected));
    }

    // A 64-bit BFI inserting a full 32-bit field at bit 32 must keep exactly the low half.
    [Test]
    public void BfiKeepMaskHandlesFullWidthFieldInUpperHalf()
    {
        var keepMask = ~(NewArmV8InstructionSet.LowBitMask(32) << 32);

        Assert.That(keepMask, Is.EqualTo(0xFFFFFFFFL));
    }

    // BFXIL writes to the bottom of the destination regardless of which part of the source it
    // reads, so its keep-mask is just the complement of the low `width` bits.
    [TestCase(1, unchecked((int)0xFFFFFFFE))]
    [TestCase(16, unchecked((int)0xFFFF0000))]
    public void BfxilKeepMaskComplementsLowField(int width, int expected)
    {
        var keepMask = ~NewArmV8InstructionSet.LowBitMask(width) & 0xFFFFFFFFL;

        Assert.That(keepMask, Is.EqualTo((uint)expected));
    }
}
