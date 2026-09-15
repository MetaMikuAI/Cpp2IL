using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class ThrowControlFlowRecoveryTests
{
    [Test]
    public void RemovesFalseFallthroughAndItsPhiInputButKeepsLivePredecessors()
    {
        var cfg = new ISILControlFlowGraph([]);
        var raising = new Block { ID = 2, Instructions = [new(0, OpCode.Throw, new Immediate(0)),
            new(1, OpCode.CallVoid, new StringLiteral("unreachable"))] };
        var live = new Block { ID = 3 };
        var dead = new Block { ID = 4 };
        var merged = new LocalVariable("merged", new Register(null, "x"));
        var phi = new Instruction(2, OpCode.Phi, merged, new Immediate(11), new Immediate(22), new Immediate(33));
        var join = new Block { ID = 5, Instructions = [phi, new(3, OpCode.Return, merged)] };
        cfg.Blocks.AddRange([raising, live, dead, join]);
        Edge(cfg.EntryBlock, raising);
        Edge(cfg.EntryBlock, live);
        Edge(raising, join);
        Edge(live, join);
        Edge(dead, join);
        Edge(join, cfg.ExitBlock);

        ThrowControlFlowRecovery.Run(cfg);
        Assert.That(raising.Instructions, Has.Count.EqualTo(1));
        Assert.That(raising.BlockType, Is.EqualTo(BlockType.Interrupt));
        Assert.That(raising.Successors, Is.EqualTo(new[] { cfg.ExitBlock }));
        Assert.That(cfg.Blocks, Does.Not.Contain(dead));
        Assert.That(join.Predecessors, Is.EqualTo(new[] { live }));
        Assert.That(phi.OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(((Immediate)phi.Operands[1]).Value, Is.EqualTo(22));
        ThrowControlFlowRecovery.Run(cfg);
        Assert.That(cfg.ExitBlock.Predecessors.Count(b => b == raising), Is.EqualTo(1));
        Assert.That(phi.Operands, Has.Count.EqualTo(2));
    }

    [Test]
    public void KeepsUnknownCallsAndTheirFallthrough()
    {
        var call = new Instruction(0, OpCode.CallVoid, new Immediate(1234));
        var ret = new Instruction(1, OpCode.Return);
        var cfg = new ISILControlFlowGraph([call, ret]);
        var before = cfg.Blocks.Select(b => b.Successors.ToArray()).ToArray();
        ThrowControlFlowRecovery.Run(cfg);
        Assert.That(cfg.Instructions, Does.Contain(call));
        Assert.That(cfg.Instructions, Does.Contain(ret));
        Assert.That(cfg.Blocks.Select(b => b.Successors.ToArray()).ToArray(), Is.EqualTo(before));
    }

    [Test]
    public void DropsCodeReachableOnlyThroughThrowFallthrough()
    {
        var call = new Instruction(0, OpCode.CallVoid, new Immediate(1234));
        var dead = new Instruction(1, OpCode.CallVoid, new StringLiteral("dead"));
        var cfg = new ISILControlFlowGraph([call, dead, new(2, OpCode.Return)]);
        call.OpCode = OpCode.Throw;
        call.SetOperands(new Immediate(0));
        ThrowControlFlowRecovery.Run(cfg);
        Assert.That(cfg.Instructions, Does.Contain(call));
        Assert.That(cfg.Instructions, Does.Not.Contain(dead));
    }

    private static void Edge(Block from, Block to)
    {
        from.Successors.Add(to);
        to.Predecessors.Add(from);
    }
}
