using System;
using System.Buffers.Binary;
using Cpp2IL.Core.InstructionSets;
using Disarm;

namespace Cpp2IL.Core.Tests.Isil;

public class Arm64ReturningIslandTests
{
    private static byte[] Island(uint instruction, ulong address, ulong continuation)
    {
        var bytes = new byte[8];
        BinaryPrimitives.WriteUInt32LittleEndian(bytes, instruction);
        BinaryPrimitives.WriteUInt32LittleEndian(bytes.AsSpan(4),
            0x14000000u | ((uint)((long)continuation - (long)(address + 4) >> 2) & 0x03FFFFFF));
        return bytes;
    }

    [TestCase(0xF9400339u)] // ldr x25, [x25]
    [TestCase(0x90000019u)] // adrp x25, page
    [TestCase(0x58000059u)] // ldr x25, literal +8
    [TestCase(0xF9000001u)] // str x1, [x0]: store must be kept, not discarded
    [TestCase(0x91000400u)] // add x0, x0, #1
    [TestCase(0xD503201Fu)] // nop
    public void PreservesRelocatedInstructionAndItsNativePc(uint instruction)
    {
        var decoded = NewArmV8InstructionSet.DecodeReturningIsland(Island(instruction, 0x9000, 0x1004), 0x9000, 0x1004);
        Assert.That(decoded.HasValue, Is.True);
        Assert.That(decoded!.Value.Address, Is.EqualTo(0x9000));
        if (instruction == 0x58000059) Assert.That(decoded.Value.Op1Imm, Is.EqualTo(8));
    }

    [TestCase(0x14000001u)] // b: not a straight-line instruction
    [TestCase(0x94000001u)] // bl: overwrites LR
    [TestCase(0xD65F03C0u)] // ret
    [TestCase(0xD61F0000u)] // br x0
    [TestCase(0xB4000020u)] // cbz x0
    [TestCase(0xD4200000u)] // brk
    [TestCase(0xFFFFFFFFu)]
    public void RejectsControlTransfersAndInvalidInstructions(uint instruction)
        => Assert.That(NewArmV8InstructionSet.DecodeReturningIsland(Island(instruction, 0x9000, 0x1004), 0x9000, 0x1004), Is.Null);

    [Test]
    public void RequiresExactFallthroughRatherThanAnyAddressInCaller()
        => Assert.That(NewArmV8InstructionSet.DecodeReturningIsland(Island(0xF9400339, 0x9000, 0x1008), 0x9000, 0x1004), Is.Null);

    [TestCase(0x94000000u)] // bl instead of b
    [TestCase(0x54000000u)] // conditional b
    [TestCase(0xD65F03C0u)] // ret
    public void RequiresUnconditionalReturnBranch(uint branch)
    {
        var bytes = Island(0xF9400339, 0x9000, 0x1004);
        BinaryPrimitives.WriteUInt32LittleEndian(bytes.AsSpan(4), branch);
        Assert.That(NewArmV8InstructionSet.DecodeReturningIsland(bytes, 0x9000, 0x1004), Is.Null);
    }

    [Test]
    public void RejectsTruncatedIsland()
        => Assert.That(NewArmV8InstructionSet.DecodeReturningIsland(new byte[4], 0x9000, 0x1004), Is.Null);
}
