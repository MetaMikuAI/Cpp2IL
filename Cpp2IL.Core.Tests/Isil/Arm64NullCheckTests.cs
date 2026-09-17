using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using Cpp2IL.Core.InstructionSets;

namespace Cpp2IL.Core.Tests.Isil;

public class Arm64NullCheckTests
{
    private static byte[] Helper(ulong address, ulong raiser)
    {
        var bytes = new byte[16];
        BinaryPrimitives.WriteUInt32LittleEndian(bytes, 0xB4000040u);
        BinaryPrimitives.WriteUInt32LittleEndian(bytes.AsSpan(4), 0xD65F03C0u);
        BinaryPrimitives.WriteUInt32LittleEndian(bytes.AsSpan(8), 0xF81F0FFEu);
        BinaryPrimitives.WriteUInt32LittleEndian(bytes.AsSpan(12),
            0x94000000u | ((uint)((long)raiser - (long)(address + 12) >> 2) & 0x03FFFFFFu));
        return bytes;
    }

    [TestCase(0x1000ul, 0x2000ul)]
    [TestCase(0x2000ul, 0x1000ul)]
    public void ResolvesForwardAndBackwardRaisers(ulong address, ulong raiser)
        => Assert.That(NewArmV8InstructionSet.DecodeNullCheckRaiser(Helper(address, raiser), address), Is.EqualTo(raiser));

    [TestCase(0, 0xB5000040u)] // CBNZ: opposite condition
    [TestCase(0, 0x34000040u)] // W0: not a pointer-sized null check
    [TestCase(0, 0xB4000041u)] // X1: not the first argument
    [TestCase(0, 0xB4000060u)] // skips the expected throw prologue
    [TestCase(4, 0xD503201Fu)] // non-null path does not return
    [TestCase(8, 0xF81F0FFDu)] // different side effect
    [TestCase(12, 0x14000001u)] // not a BL
    public void RejectsDifferentSemantics(int offset, uint instruction)
    {
        var bytes = Helper(0x1000, 0x2000);
        BinaryPrimitives.WriteUInt32LittleEndian(bytes.AsSpan(offset), instruction);
        Assert.That(NewArmV8InstructionSet.DecodeNullCheckRaiser(bytes, 0x1000), Is.Zero);
    }

    [TestCase("NullReferenceException", true, true)]
    [TestCase("NullReferenceException", false, false)]
    [TestCase("InvalidCastException", true, false)]
    public void OnlyConfirmedNullRaiserBecomesGuardWithoutClobberingX0(string exceptionName, bool raises, bool recovered)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var target = app.Binary.GetVirtualAddressOfPrimaryExecutableSection() + 0x100;
        var raiser = target + 0x80;
        app.Binary.BaseStream.Position = app.Binary.MapVirtualAddressToRaw(target);
        app.Binary.BaseStream.Write(Helper(target, raiser));
        app.MethodsByAddress.Remove(target);
        app.ThrowHelperNamesByAddress[raiser] = exceptionName;
        app.ExceptionRaisersByAddress[raiser] = raises;
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        var decoded = Disassembler.Disassemble(BitConverter.GetBytes(0x94000008u), target - 32,
            new Disassembler.Options(true, true, false)).Single();
        var instructions = new List<Instruction>();
        var addresses = new List<ulong>();
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement", BindingFlags.NonPublic | BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(), new object[] { decoded, instructions, addresses, caller, new HashSet<string>() });
        if (!recovered)
        {
            Assert.That(instructions.Single().OpCode, Is.EqualTo(OpCode.Call));
            return;
        }
        Assert.That(instructions.Select(i => i.OpCode), Is.EqualTo(new[]
            { OpCode.CheckNotEqual, OpCode.ConditionalJump, OpCode.Throw, OpCode.Nop }));
        Assert.That(instructions[0].Operands[1], Is.EqualTo(new Register(null, "X0")));
        Assert.That(instructions[0].Operands[2], Is.EqualTo(new Immediate(0)));
        Assert.That(instructions[1].Operands[1], Is.EqualTo(instructions[0].Destination));
        Assert.That(((Immediate)instructions[1].Operands[0]).UnsignedValue, Is.EqualTo(addresses[3]));
        Assert.That(((TypeAnalysisContext)instructions[2].Operands[0]).FullName, Is.EqualTo("System.NullReferenceException"));
        Assert.That(instructions.Any(i => i.Destination is Register { Name: "X0" }), Is.False);
    }

    [Test]
    public void RejectsTruncatedHelper()
        => Assert.That(NewArmV8InstructionSet.DecodeNullCheckRaiser(new byte[12], 0x1000), Is.Zero);
}
