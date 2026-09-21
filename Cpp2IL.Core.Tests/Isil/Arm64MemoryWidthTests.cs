using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Isil;

public class Arm64MemoryWidthTests
{
    [TestCase(0x39400020u, 1)] // ldrb w0, [x1]
    [TestCase(0x39800020u, 1)] // ldrsb x0, [x1]
    [TestCase(0x79400020u, 2)] // ldrh w0, [x1]
    [TestCase(0x79800020u, 2)] // ldrsh x0, [x1]
    [TestCase(0xB9400020u, 4)]
    [TestCase(0xB9800020u, 4)] // ldrsw x0, [x1]
    [TestCase(0xF9400020u, 8)]
    [TestCase(0xBD400020u, 4)] // ldr s0, [x1]
    [TestCase(0xFD400020u, 8)]
    [TestCase(0x3DC00020u, 16)] // ldr q0, [x1]
    [TestCase(0x18000020u, 4)] // literal
    [TestCase(0xF8408C20u, 8)] // pre-index
    [TestCase(0xF8408420u, 8)] // post-index
    [TestCase(0x39000020u, 1)]
    [TestCase(0x79000020u, 2)]
    [TestCase(0xB9000020u, 4)]
    [TestCase(0xF9000020u, 8)]
    public void PreservesNativeAccessRatherThanDestinationRegisterWidth(uint word, int size)
        => Assert.That(Lift(word).Single().AccessSize, Is.EqualTo(size));

    [TestCase(0xA9400820u, 8)] // ldp x0, x2, [x1]
    [TestCase(0x29400820u, 4)] // ldp w0, w2, [x1]
    [TestCase(0x69400820u, 4)] // ldpsw x0, x2, [x1]
    [TestCase(0xA9000820u, 8)] // stp x0, x2, [x1]
    public void PairAccessesUseElementWidthForSecondOffset(uint word, int size)
    {
        var memory = Lift(word);
        Assert.That(memory.Select(m => m.AccessSize), Is.EqualTo(new[] { size, size }));
        Assert.That(memory.Select(m => m.Addend), Is.EqualTo(new long[] { 0, size }));
    }

    [TestCase(0xFD400020u)]
    [TestCase(0xFD000020u)]
    public void SplitDoubleRegistersCarryFourByteLaneAccesses(uint word)
    {
        var memory = Lift(word, true);
        Assert.That(memory.Select(m => m.AccessSize), Is.EqualTo(new[] { 4, 4 }));
        Assert.That(memory.Select(m => m.Addend), Is.EqualTo(new long[] { 0, 4 }));
    }

    private static List<MemoryOperand> Lift(uint word, bool split = false)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        foreach (var name in new[] { "adrpOffsets", "integerConstants" })
            typeof(NewArmV8InstructionSet).GetField(name, BindingFlags.NonPublic | BindingFlags.Static)!
                .SetValue(null, new Dictionary<string, ulong>());
        var decoded = Disassembler.Disassemble(BitConverter.GetBytes(word), 0, new Disassembler.Options(true, true, false)).Single();
        var instructions = new List<Instruction>();
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement", BindingFlags.NonPublic | BindingFlags.Instance)!
            .Invoke(new NewArmV8InstructionSet(), new object[] { decoded, instructions, new List<ulong>(), caller,
                split ? new HashSet<string> { "V0" } : new HashSet<string>() });
        return instructions.SelectMany(i => i.Operands).OfType<MemoryOperand>().ToList();
    }
}
