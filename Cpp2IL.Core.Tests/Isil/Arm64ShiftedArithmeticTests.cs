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
