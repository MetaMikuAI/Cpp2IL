using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class FlagConditionRecoveryTests
{
    private static readonly LocalVariable A = new("a", new Register(null, "a"));
    private static readonly LocalVariable B = new("b", new Register(null, "b"));

    private static LocalVariable Flag(string name) => new(name, new Register(null, name));

    /// <summary>
    /// Builds a graph from a flag-cluster + conditional jump, resolving the jump target like the
    /// lifter does, and returns the instruction defining <paramref name="condition"/> after recovery.
    /// </summary>
    private static Instruction RecoverAndGetConditionDef(List<Instruction> flagAndBranch, LocalVariable condition)
    {
        // Append two trivial return blocks so the conditional jump has a real target/fallthrough.
        var index = flagAndBranch.Count;
        var instructions = new List<Instruction>(flagAndBranch)
        {
            new(index, OpCode.Return),
            new(index + 1, OpCode.Return),
        };

        // The conditional jump's target (operand 0) is the last instruction's index.
        var conditionalJump = instructions.First(i => i.OpCode == OpCode.ConditionalJump);
        conditionalJump.SetOperand(0, instructions[index + 1]);

        var graph = new ISILControlFlowGraph(instructions);
        FlagConditionRecovery.Run(graph);

        return graph.Blocks.SelectMany(b => b.Instructions)
            .First(i => i.Destination is LocalVariable d && ReferenceEquals(d, condition));
    }

    [TestCase(false, false)]
    [TestCase(false, true)]
    [TestCase(true, false)]
    [TestCase(true, true)]
    public void RecoversUnsignedRangeWithoutLosingWidth(bool lessOrEqual, bool inverted)
    {
        Cpp2IlApi.ResetInternalState();
        var type = TestGameLoader.LoadSimple2019Game().SystemTypes.SystemUInt32Type;
        var borrow = Flag("borrow"); var carry = Flag("carry"); var difference = Flag("difference");
        var zero = Flag("zero"); var nonzero = Flag("nonzero"); var condition = Flag("condition");
        var inverse = Flag("inverse");
        var instructions = new List<Instruction>
        {
            new(0, OpCode.CheckLess, borrow, A, B, type),
            new(1, OpCode.Not, carry, borrow),
            new(2, OpCode.Subtract, difference, A, B),
            new(3, OpCode.CheckEqual, zero, difference, Imm(0)),
            new(4, OpCode.Not, nonzero, zero),
            new(5, lessOrEqual ? OpCode.Or : OpCode.And, condition, lessOrEqual ? borrow : carry, lessOrEqual ? zero : nonzero),
        };
        if (inverted) instructions.Add(new(6, OpCode.Not, inverse, condition));
        instructions.Add(new(7, OpCode.ConditionalJump, Imm(0), inverted ? inverse : condition));
        var definition = RecoverAndGetConditionDef(instructions, inverted ? inverse : condition);
        Assert.That(definition.OpCode, Is.EqualTo(lessOrEqual != inverted ? OpCode.CheckLessOrEqual : OpCode.CheckGreater));
        Assert.That(definition.Operands.ToArray(), Is.EqualTo(new IOperand[] { inverted ? inverse : condition, A, B, type }));
    }

    [Test]
    public void UnsignedSubtractComparedWithZeroIsNotASignedSignFlag()
    {
        Cpp2IlApi.ResetInternalState();
        var type = TestGameLoader.LoadSimple2019Game().SystemTypes.SystemUInt32Type;
        var difference = Flag("difference"); var condition = Flag("condition");
        var definition = RecoverAndGetConditionDef([
            new(0, OpCode.Subtract, difference, A, B),
            new(1, OpCode.CheckLess, condition, difference, Imm(0), type),
            new(2, OpCode.ConditionalJump, Imm(0), condition)], condition);
        Assert.That(definition.Operands[1], Is.SameAs(difference));
        Assert.That(definition.Operands[3], Is.SameAs(type));
    }

    [Test]
    public void RecoversEquality()
    {
        // cmp a, b ; je   ->  ZF = (a - b) == 0 ; if ZF
        var t1 = Flag("TEMP1");
        var zf = Flag("ZF");

        var def = RecoverAndGetConditionDef(new List<Instruction>
        {
            new(0, OpCode.Subtract, t1, A, B),
            new(1, OpCode.CheckEqual, zf, t1, Imm(0)),
            new(2, OpCode.ConditionalJump, Imm(0), zf),
        }, zf);

        Assert.That(def.OpCode, Is.EqualTo(OpCode.CheckEqual));
        Assert.That(def.Operands[1], Is.EqualTo(A));
        Assert.That(def.Operands[2], Is.EqualTo(B));
    }

    [Test]
    public void RecoversInequality()
    {
        // cmp a, b ; jne  ->  ZF = (a - b) == 0 ; cond = !ZF ; if cond
        var t1 = Flag("TEMP1");
        var zf = Flag("ZF");
        var cond = Flag("TEMP");

        var def = RecoverAndGetConditionDef(new List<Instruction>
        {
            new(0, OpCode.Subtract, t1, A, B),
            new(1, OpCode.CheckEqual, zf, t1, Imm(0)),
            new(2, OpCode.Not, cond, zf),
            new(3, OpCode.ConditionalJump, Imm(0), cond),
        }, cond);

        Assert.That(def.OpCode, Is.EqualTo(OpCode.CheckNotEqual));
        Assert.That(def.Operands[1], Is.EqualTo(A));
        Assert.That(def.Operands[2], Is.EqualTo(B));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void RecoversSignedLessThan(bool inverted)
    {
        // cmp a, b ; jl  ->  full flag cluster ; cond = !(SF == OF) ; if cond
        var t1 = Flag("TEMP1");
        var t2 = Flag("TEMP2");
        var t3 = Flag("TEMP3");
        var t4 = Flag("TEMP4");
        var of = Flag("OF");
        var sf = Flag("SF");
        var sfEqOf = Flag("TEMP_a");
        var cond = Flag("TEMP_b");
        var inverse = Flag("TEMPCSEL");

        var instructions = new List<Instruction>
        {
            new(0, OpCode.Subtract, t1, A, B),
            new(1, OpCode.Xor, t2, A, B),
            new(2, OpCode.Xor, t3, A, t1),
            new(3, OpCode.And, t4, t2, t3),
            new(4, OpCode.CheckLess, of, t4, Imm(0)),
            new(5, OpCode.CheckLess, sf, t1, Imm(0)),
            new(6, OpCode.CheckEqual, sfEqOf, sf, of),
            new(7, OpCode.Not, cond, sfEqOf),
        };
        if (inverted) instructions.Add(new(8, OpCode.Not, inverse, cond));
        instructions.Add(new(9, OpCode.ConditionalJump, Imm(0), inverted ? inverse : cond));
        var def = RecoverAndGetConditionDef(instructions, inverted ? inverse : cond);

        Assert.That(def.OpCode, Is.EqualTo(inverted ? OpCode.CheckGreaterOrEqual : OpCode.CheckLess));
        Assert.That(def.Operands[1], Is.EqualTo(A));
        Assert.That(def.Operands[2], Is.EqualTo(B));
    }

    [Test]
    public void RecoversSignedGreaterOrEqual()
    {
        // cmp a, b ; jge  ->  cond = (SF == OF) ; if cond
        var t1 = Flag("TEMP1");
        var t2 = Flag("TEMP2");
        var t3 = Flag("TEMP3");
        var t4 = Flag("TEMP4");
        var of = Flag("OF");
        var sf = Flag("SF");
        var cond = Flag("TEMP");

        var def = RecoverAndGetConditionDef(new List<Instruction>
        {
            new(0, OpCode.Subtract, t1, A, B),
            new(1, OpCode.Xor, t2, A, B),
            new(2, OpCode.Xor, t3, A, t1),
            new(3, OpCode.And, t4, t2, t3),
            new(4, OpCode.CheckLess, of, t4, Imm(0)),
            new(5, OpCode.CheckLess, sf, t1, Imm(0)),
            new(6, OpCode.CheckEqual, cond, sf, of),
            new(7, OpCode.ConditionalJump, Imm(0), cond),
        }, cond);

        Assert.That(def.OpCode, Is.EqualTo(OpCode.CheckGreaterOrEqual));
        Assert.That(def.Operands[1], Is.EqualTo(A));
        Assert.That(def.Operands[2], Is.EqualTo(B));
    }

    [Test]
    public void LeavesUnrecognisedConditionsAlone()
    {
        // A conditional jump on a plain boolean local with no flag pattern must be untouched.
        var cond = Flag("someBool");
        var def = RecoverAndGetConditionDef(new List<Instruction>
        {
            new(0, OpCode.Move, cond, Imm(1)),
            new(1, OpCode.ConditionalJump, Imm(0), cond),
        }, cond);

        Assert.That(def.OpCode, Is.EqualTo(OpCode.Move));
    }

    [Test, Combinatorial]
    public void RecoversCompoundSignedConditionsOnlyWithMatchingFlags(
        [Values] bool greater, [Values] bool inverted, [Values] bool swapped,
        [Values("none", "zero", "overflow")] string mutation)
    {
        var difference = Flag("difference");
        var otherDifference = Flag("otherDifference");
        var ab = Flag("ab");
        var ar = Flag("ar");
        var bits = Flag("bits");
        var sign = Flag("sign");
        var overflow = Flag("overflow");
        var zero = Flag("zero");
        var notZero = Flag("notZero");
        var signEqualsOverflow = Flag("signEqualsOverflow");
        var less = Flag("less");
        var compound = Flag("compound");
        var inverse = Flag("inverse");
        var left = greater ? signEqualsOverflow : less;
        var right = greater ? notZero : zero;
        var condition = inverted ? inverse : compound;
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Subtract, difference, A, B),
            new(1, OpCode.Subtract, otherDifference, B, A),
            new(2, OpCode.Xor, ab, A, B),
            new(3, OpCode.Xor, ar, mutation == "overflow" ? B : A, difference),
            new(4, OpCode.And, bits, ab, ar),
            new(5, OpCode.CheckLess, overflow, bits, Imm(0)),
            new(6, OpCode.CheckLess, sign, difference, Imm(0)),
            new(7, OpCode.CheckEqual, zero, mutation == "zero" ? otherDifference : difference, Imm(0)),
            new(8, OpCode.Not, notZero, zero),
            new(9, OpCode.CheckEqual, signEqualsOverflow, sign, overflow),
            new(10, OpCode.Not, less, signEqualsOverflow),
            new(11, greater ? OpCode.And : OpCode.Or, compound, swapped ? right : left, swapped ? left : right),
            new(12, OpCode.Not, inverse, compound),
            new(13, OpCode.ConditionalJump, Imm(0), condition),
        };
        var definition = RecoverAndGetConditionDef(instructions, condition);
        if (mutation != "none")
        {
            Assert.That(definition.OpCode, Is.EqualTo(inverted ? OpCode.Not : greater ? OpCode.And : OpCode.Or));
            return;
        }
        var expectedGreater = greater != inverted;
        Assert.That(definition.OpCode, Is.EqualTo(expectedGreater ? OpCode.CheckGreater : OpCode.CheckLessOrEqual));
        Assert.That(definition.Operands.Skip(1), Is.EqualTo(new IOperand[] { A, B }));
        foreach (var a in new[] { int.MinValue, -1, 0, 1, int.MaxValue })
        foreach (var b in new[] { int.MinValue, -1, 0, 1, int.MaxValue })
        {
            var delta = unchecked(a - b);
            var sf = delta < 0;
            var of = ((a ^ b) & (a ^ delta)) < 0;
            var zf = delta == 0;
            var original = greater ? sf == of && !zf : sf != of || zf;
            Assert.That(inverted ? !original : original, Is.EqualTo(expectedGreater ? a > b : a <= b));
        }
    }
}
