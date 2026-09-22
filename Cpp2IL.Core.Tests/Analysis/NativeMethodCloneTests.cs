using System;
using System.Collections.Generic;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Utils;
using Cpp2IL.Core.ISIL;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeMethodCloneTests
{
    private static List<Arm64Instruction> Decode(string hex, ulong start) => Disassembler.Disassemble(
        Convert.FromHexString(hex).AsSpan(), start, new Disassembler.Options(true, true, false)).ToList();

    private static string? Fingerprint(string hex, ulong start, bool initializer = true, bool hidden = true)
        => NativeMethodCloneRecovery.Fingerprint(Decode(hex, start), address => initializer && address == 0x49091CC,
            address => hidden && address == 0xA796F70 ? Arm64Register.X1 : null);

    [Test]
    public void CompleteCopiesMatchAcrossRelocationGuardAndHiddenMetadataArgument()
    {
        var registered = Fingerprint(NativeMethodCloneFixtures.Registered, 0xA7B6EFC);
        Assert.That(registered, Is.Not.Null);
        Assert.That(Fingerprint(NativeMethodCloneFixtures.Duplicate, 0x4A1108C), Is.EqualTo(registered));
    }

    [TestCase(false, true)]
    [TestCase(true, false)]
    public void UnprovenInitializationOrArgumentIsNotIgnored(bool initializer, bool hidden)
        => Assert.That(Fingerprint(NativeMethodCloneFixtures.Duplicate, 0x4A1108C, initializer, hidden),
            Is.Not.EqualTo(Fingerprint(NativeMethodCloneFixtures.Registered, 0xA7B6EFC, initializer, hidden)));

    [TestCase(14, 0x400u)] // Different receiver field offset.
    [TestCase(21, 0x20u)]  // Different conditional branch destination.
    [TestCase(44, 0x1u)]   // Different called function.
    [TestCase(60, 0x8000u)] // Different field in the block AFTER the first RET.
    public void DifferentBehaviorDoesNotMatch(int instruction, uint mask)
    {
        var bytes = Convert.FromHexString(NativeMethodCloneFixtures.Duplicate);
        var word = BitConverter.ToUInt32(bytes, instruction * 4) ^ mask;
        BitConverter.GetBytes(word).CopyTo(bytes, instruction * 4);
        Assert.That(Fingerprint(Convert.ToHexString(bytes), 0x4A1108C),
            Is.Not.EqualTo(Fingerprint(NativeMethodCloneFixtures.Registered, 0xA7B6EFC)));
    }

    [TestCase("epilogue", true)]
    [TestCase("low", false)]
    [TestCase("high", false)]
    [TestCase("float", false)]
    [TestCase("implicit", false)]
    [TestCase("call", false)]
    [TestCase("indirect", false)]
    [TestCase("branch", false)]
    [TestCase("unknown", false)]
    [TestCase("otherReturn", false)]
    [TestCase("noReturn", false)]
    public void RequiresTheWholeNativeReturnToReachTheManagedReturn(string kind, bool expected)
    {
        var result = new Register(null, "X0");
        var middle = kind switch
        {
            "low" => new Instruction(1, OpCode.Move, result, new Immediate(0)),
            "high" => new Instruction(1, OpCode.Move, new Register(null, "X1"), new Immediate(0)),
            "float" => new Instruction(1, OpCode.Move, new Register(null, "V2"), new Immediate(0)),
            "call" => new Instruction(1, OpCode.CallVoid, new Immediate(0x2000)),
            "indirect" => new Instruction(1, OpCode.IndirectCall, new Register(null, "X9"), result),
            "branch" => new Instruction(1, OpCode.Jump, new Immediate(3)),
            "unknown" => new Instruction(1, OpCode.NotImplemented, new StringLiteral("unknown effects")),
            _ => new Instruction(1, OpCode.Move, new Register(null, "X19"), new StackOffset(16))
        };
        if (kind == "implicit") middle.ImplicitDefinition = new Register(null, "X1");
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Call, new Immediate(0x1000), result), middle,
            new(2, OpCode.ShiftStack, new Register(null, "sp"), new Immediate(32))
        };
        if (kind != "noReturn") instructions.Add(new(3, OpCode.Return, kind == "otherReturn" ? new Register(null, "X2") : result));
        Assert.That(NativeMethodCloneRecovery.ReturnsUnchanged(instructions, 0, result), Is.EqualTo(expected));
    }

    [Test]
    public void TruncatedReturnTailIsRejected()
    {
        var bytes = Convert.FromHexString(NativeMethodCloneFixtures.Duplicate);
        Assert.That(Fingerprint(Convert.ToHexString(bytes.AsSpan(0, 56 * 4)), 0x4A1108C), Is.Null);
    }
}
