using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class SingleFieldConstructorRecoveryTests
{
    private const string Fixture = "FE0F1EF8F44F01A9F303012AE1031FAAF40300AA6C213D95931200B9F44F41A9FE0742F8C0035FD6";

    [Test]
    public void DecodesCompleteCapturedConstructor()
        => Assert.That(SingleFieldConstructorRecovery.Decode(Convert.FromHexString(Fixture), 0x5262FB4),
            Is.EqualTo((0xA1AB578UL, 16)));

    [TestCase(0)] [TestCase(1)] [TestCase(2)] [TestCase(3)] [TestCase(4)]
    [TestCase(5)] [TestCase(6)] [TestCase(7)] [TestCase(8)] [TestCase(9)]
    public void RejectsUnprovenInstructionAtEveryPosition(int index)
    {
        var body = Convert.FromHexString(Fixture);
        BinaryPrimitives.WriteUInt32LittleEndian(body.AsSpan(index * 4), 0xD503201F);
        Assert.That(SingleFieldConstructorRecovery.Decode(body, 0x5262FB4), Is.Null);
    }

    [TestCase(0)] [TestCase(4)] [TestCase(36)] [TestCase(39)]
    public void RejectsTruncatedBodies(int length)
        => Assert.That(SingleFieldConstructorRecovery.Decode(Convert.FromHexString(Fixture).AsSpan(0, length), 0x5262FB4), Is.Null);

    [Test]
    public void DecodesBackwardCallAndDifferentFieldOffset()
    {
        var body = Convert.FromHexString(Fixture);
        BinaryPrimitives.WriteUInt32LittleEndian(body.AsSpan(20), 0x97FFFFFB); // BL back to start
        BinaryPrimitives.WriteUInt32LittleEndian(body.AsSpan(24), 0xB9002293); // STR W19,[X20,#32]
        Assert.That(SingleFieldConstructorRecovery.Decode(body, 0x1000), Is.EqualTo((0x1000UL, 32)));
    }

    [TestCase(false)] [TestCase(true)]
    public void OnlyFollowsUnambiguousInitializationPath(bool otherPredecessor)
    {
        var allocation = new Instruction(0, OpCode.Nop);
        var call = new Instruction(1, OpCode.CallVoid, new Immediate(123));
        var store = new Instruction(2, OpCode.Move, new Immediate(16), new Immediate(0));
        var first = new Block { Instructions = [allocation, call] };
        var second = new Block { Instructions = [store], Predecessors = [first] };
        first.Successors.Add(second);
        if (otherPredecessor) second.Predecessors.Add(new Block());
        var graph = new ISILControlFlowGraph(new List<Instruction>()) { Blocks = [first, second], EntryBlock = first };
        var following = SingleFieldConstructorRecovery.Following(graph, allocation).ToArray();
        Assert.That(following, Is.EqualTo(otherPredecessor ? new[] { call } : new[] { call, store }));
    }
}
