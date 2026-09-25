using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Isil;

public class Arm64ScalarLaneTests
{
    private static List<Instruction> Lift(uint word, params string[] twoSLaneRegisters)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, []) { RawBytes = new BinarySlice(BitConverter.GetBytes(word)) };
        foreach (var name in new[] { "adrpOffsets", "integerConstants" })
            typeof(NewArmV8InstructionSet).GetField(name, BindingFlags.Static | BindingFlags.NonPublic)!
                .SetValue(null, new Dictionary<string, ulong>());
        var decoded = Disassembler.Disassemble(BitConverter.GetBytes(word), 0, new Disassembler.Options(true, true, false)).Single();
        var instructions = new List<Instruction>();
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement", BindingFlags.Instance | BindingFlags.NonPublic)!
            .Invoke(new NewArmV8InstructionSet(), new object[] { decoded, instructions, new List<ulong>(), method, new HashSet<string>(twoSLaneRegisters) });
        return instructions;
    }

    private static string Name(IOperand operand) => ((Register)operand).Name;

    [Test]
    public void ScalarAbsoluteDifferenceKeepsBothSources()
    {
        // fabd s0, s2, s0
        var subtract = Lift(0x7EA0D440).First(i => i.OpCode == OpCode.Subtract);
        Assert.That(subtract.Operands.Select(Name), Is.EqualTo(new[] { "V0", "V2", "V0" }));
    }

    [Test]
    public void ElementZeroIsTheScalarRegister()
    {
        // fmul v0.2s, v0.2s, v2.s[0]: a value a scalar instruction left in S2 is what lane 0 reads
        var multiplies = Lift(0x0F829000, "V0").Where(i => i.OpCode == OpCode.Multiply).ToList();
        Assert.That(multiplies.Select(i => i.Operands.Select(Name).ToArray()), Is.EqualTo(new[]
        {
            new[] { "V0", "V0", "V2" },
            new[] { "V0.S1", "V0.S1", "V2" },
        }));
    }

    [Test]
    public void ScalarSelectWritesLaneZero()
    {
        // fcsel s2, s0, s1, pl in a method that also uses V2 as .2S
        var moves = Lift(0x1E215C02, "V2").Where(i => i.OpCode == OpCode.Move).ToList();
        Assert.That(moves, Has.Count.EqualTo(2));
        Assert.That(moves.Select(m => Name(m.Operands[0])), Is.All.EqualTo("V2"));
    }

    [Test]
    public void WholeVectorCopyCarriesSecondLane()
    {
        // mov v8.16b, v0.16b
        var moves = Lift(0x4EA01C08, "V8").Where(i => i.OpCode == OpCode.Move).ToList();
        Assert.That(moves.Select(m => (Name(m.Operands[0]), Name(m.Operands[1]))),
            Is.EqualTo(new[] { ("V8", "V0"), ("V8.S1", "V0.S1") }));
    }

    [Test]
    public void ScalarVectorCopyWithoutLaneUseStaysSingle()
    {
        // mov v8.16b, v0.16b where neither register is used as .2S
        var moves = Lift(0x4EA01C08).Where(i => i.OpCode == OpCode.Move).ToList();
        Assert.That(moves, Has.Count.EqualTo(1));
    }
}
