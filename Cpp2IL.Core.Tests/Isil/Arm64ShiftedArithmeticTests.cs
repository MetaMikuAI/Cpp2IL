using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Isil;

public class Arm64ShiftedArithmeticTests
{
    [TestCase(0x0A887D01u, OpCode.And, OpCode.ShiftRight, "System.Int32")] // and w1, w8, w8, asr #31
    [TestCase(0x8A887D01u, OpCode.And, OpCode.ShiftRight, "System.Int64")]
    [TestCase(0x0A487D01u, OpCode.And, OpCode.ShiftRight, "System.UInt32")]
    [TestCase(0x8A487D01u, OpCode.And, OpCode.ShiftRight, "System.UInt64")]
    [TestCase(0x0A087D01u, OpCode.And, OpCode.ShiftLeft, "System.UInt32")]
    [TestCase(0x8A087D01u, OpCode.And, OpCode.ShiftLeft, "System.UInt64")]
    [TestCase(0x2A887D01u, OpCode.Or, OpCode.ShiftRight, "System.Int32")]
    [TestCase(0x4A887D01u, OpCode.Xor, OpCode.ShiftRight, "System.Int32")]
    [TestCase(0x6A887D01u, OpCode.And, OpCode.ShiftRight, "System.Int32")] // ands
    [TestCase(0x6A887D1Fu, OpCode.And, OpCode.ShiftRight, "System.Int32")] // tst alias
    [TestCase(0x0AA87D01u, OpCode.Not, OpCode.ShiftRight, "System.Int32")] // bic: shift before invert
    [TestCase(0x2AA87D01u, OpCode.Not, OpCode.ShiftRight, "System.Int32")] // orn
    [TestCase(0x4AA87D01u, OpCode.Not, OpCode.ShiftRight, "System.Int32")] // eon
    [TestCase(0x6AA87D01u, OpCode.Not, OpCode.ShiftRight, "System.Int32")] // bics
    [TestCase(0x2AA87FE1u, OpCode.Not, OpCode.ShiftRight, "System.Int32")] // mvn alias
    public void LogicalOperandsPreserveShiftAndNativeType(uint word, OpCode operation, OpCode shiftOpcode, string type)
    {
        var instructions = Lift(word);
        var shift = instructions.Single(i => i.OpCode == shiftOpcode);
        Assert.That(shift.Operands[2], Is.EqualTo(new Immediate(31)));
        Assert.That(((TypeAnalysisContext)shift.Operands[3]).FullName, Is.EqualTo(type));
        var consumer = instructions.First(i => i.OpCode == operation);
        Assert.That(consumer.Operands[operation == OpCode.Not ? 1 : 2], Is.EqualTo(shift.Destination));
        Assert.That(instructions.IndexOf(shift), Is.LessThan(instructions.IndexOf(consumer)));
    }

    [TestCase(0x0AC80D01u, "System.UInt32", 29)]
    [TestCase(0x8AC80D01u, "System.UInt64", 61)]
    public void LogicalRotateUsesBothWidthBoundedShifts(uint word, string type, int distance)
    {
        var instructions = Lift(word);
        var low = instructions.Single(i => i.OpCode == OpCode.ShiftRight);
        var high = instructions.Single(i => i.OpCode == OpCode.ShiftLeft);
        Assert.That(low.Operands[2], Is.EqualTo(new Immediate(3)));
        Assert.That(high.Operands[2], Is.EqualTo(new Immediate(distance)));
        Assert.That(((TypeAnalysisContext)low.Operands[3]).FullName, Is.EqualTo(type));
        Assert.That(high.Operands[3], Is.SameAs(low.Operands[3]));
        Assert.That(instructions.Single(i => i.OpCode == OpCode.Or).Operands[2], Is.EqualTo(high.Destination));
    }

    [TestCase(0x0A080101u)] // no shift
    [TestCase(0x12001D01u)] // immediate mask
    public void DoesNotShiftPlainLogicalOperands(uint word)
        => Assert.That(Lift(word).Any(i => i.OpCode is OpCode.ShiftLeft or OpCode.ShiftRight), Is.False);

    [TestCase(0x6B0802A8u)] // subs w8, w21, w8 (destination aliases right input)
    [TestCase(0x6B150108u)] // subs w8, w8, w21 (destination aliases left input)
    [TestCase(0xEB0802A8u)]
    [TestCase(0xEB150108u)]
    public void SubtractFlagsCaptureInputsBeforeAliasedDestinationWrite(uint word)
    {
        var instructions = Lift(word);
        var write = instructions.Single(i => i.Destination is Register { Name: "X8" });
        var lastFlag = instructions.FindLastIndex(i => i.Destination is Register { Name: "N" or "Z" or "C" or "V" });
        Assert.That(lastFlag, Is.GreaterThanOrEqualTo(0));
        Assert.That(lastFlag, Is.LessThan(instructions.IndexOf(write)));
    }

    private static List<Instruction> Lift(uint word)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets", BindingFlags.NonPublic | BindingFlags.Static)!
            .SetValue(null, new Dictionary<string, ulong>());
        typeof(NewArmV8InstructionSet).GetField("integerConstants", BindingFlags.NonPublic | BindingFlags.Static)!
            .SetValue(null, new Dictionary<string, ulong>());
        var decoded = Disassembler.Disassemble(BitConverter.GetBytes(word), 0, new Disassembler.Options(true, true, false)).Single();
        var instructions = new List<Instruction>();
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement", BindingFlags.NonPublic | BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(), new object[] { decoded, instructions, new List<ulong>(), caller, new HashSet<string>() });
        return instructions;
    }

    [TestCase(0x8B0B0D8Bu, OpCode.Add, false)] // add x11, x12, x11, lsl #3
    [TestCase(0xCB0B0D8Bu, OpCode.Subtract, false)]
    [TestCase(0xAB0B0D8Bu, OpCode.Add, false)] // adds
    [TestCase(0xEB0B0D8Bu, OpCode.Subtract, false)] // subs
    [TestCase(0x0B0B0D8Bu, OpCode.Add, true)] // add w11, w12, w11, lsl #3
    [TestCase(0x8B2C0D48u, OpCode.Add, false)] // add x8, x10, w12, uxtb #3
    [TestCase(0x8B2C4D48u, OpCode.Add, false)] // add x8, x10, w12, uxtw #3
    [TestCase(0x8B2C2D48u, OpCode.Add, false)] // add x8, x10, w12, uxth #3
    public void PreservesShiftBeforeArithmetic(uint word, OpCode opcode, bool narrow)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets", BindingFlags.NonPublic | BindingFlags.Static)!
            .SetValue(null, new Dictionary<string, ulong>());
        typeof(NewArmV8InstructionSet).GetField("integerConstants", BindingFlags.NonPublic | BindingFlags.Static)!
            .SetValue(null, new Dictionary<string, ulong>());
        var decoded = Disassembler.Disassemble(BitConverter.GetBytes(word), 0, new Disassembler.Options(true, true, false)).Single();
        var instructions = new List<Instruction>();
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement", BindingFlags.NonPublic | BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(), new object[] { decoded, instructions, new List<ulong>(), caller, new HashSet<string>() });
        var shift = instructions.Single(i => i.OpCode == OpCode.ShiftLeft);
        Assert.That(shift.Operands[2], Is.EqualTo(new Immediate(3)));
        if (decoded.FinalOpExtendType is Arm64ExtendType.UXTB or Arm64ExtendType.UXTH or Arm64ExtendType.UXTW)
        {
            Assert.That(instructions[0].OpCode, Is.EqualTo(OpCode.ZeroExtend));
            Assert.That(instructions[0].Operands[2], Is.EqualTo(new Immediate(decoded.FinalOpExtendType switch
                { Arm64ExtendType.UXTB => 8, Arm64ExtendType.UXTH => 16, _ => 32 })));
        }
        var arithmetic = instructions.First(i => i.OpCode == opcode);
        Assert.That(arithmetic.Operands[2], Is.EqualTo(shift.Destination));
        Assert.That(instructions.Any(i => i.OpCode == OpCode.And && i.Operands[2] is Immediate { Value: 0xFFFFFFFFL }), Is.EqualTo(narrow));
    }
}
