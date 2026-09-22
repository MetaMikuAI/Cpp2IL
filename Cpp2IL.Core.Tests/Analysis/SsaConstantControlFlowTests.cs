using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class SsaConstantControlFlowTests
{
    [TestCase("same", true)]
    [TestCase("inverted", true)]
    [TestCase("differentMask", false)]
    [TestCase("wrongPolarity", false)]
    [TestCase("call", false)]
    [TestCase("load", false)]
    [TestCase("store", false)]
    [TestCase("escaping", false)]
    [TestCase("differentPhi", false)]
    public void FoldsOnlyEquivalentPureSuccessors(string mutation, bool expected)
    {
        var cfg = new ISILControlFlowGraph([]);
        var input = Local("input");
        var guardValue = Local("guard");
        var leftMask = Local("leftMask");
        var rightMask = Local("rightMask");
        var leftCondition = Local("leftCondition");
        var rightCondition = Local("rightCondition");
        var negated = Local("negated");
        var head = Block(cfg);
        var left = Block(cfg,
            new(-1, OpCode.And, leftMask, input, new Immediate(128)),
            new(-1, OpCode.CheckEqual, leftCondition, leftMask, new Immediate(0)));
        var right = Block(cfg,
            new(-1, OpCode.And, rightMask, input, new Immediate(mutation == "differentMask" ? 64 : 128)),
            new(-1, OpCode.CheckEqual, rightCondition, rightMask, new Immediate(0)));
        var phi = new Instruction(-1, OpCode.Phi, Local("result"), new Immediate(7), new Immediate(mutation == "differentPhi" ? 8 : 7));
        var yes = Block(cfg, phi, new(-1, OpCode.Return, mutation == "escaping" ? rightMask : phi.Operands[0]));
        var no = Block(cfg, new Instruction(-1, OpCode.Return, new Immediate(0)));
        if (mutation is "inverted" or "wrongPolarity")
            right.AddInstruction(new(-1, OpCode.Not, negated, rightCondition));
        if (mutation == "call") right.AddInstruction(new(-1, OpCode.CallVoid, new StringLiteral("effect")));
        if (mutation == "load") right.AddInstruction(new(-1, OpCode.Move, Local("read"), new MemoryOperand(input)));
        if (mutation == "store") right.AddInstruction(new(-1, OpCode.Move, new MemoryOperand(input), new Immediate(1)));
        head.AddInstruction(new(-1, OpCode.ConditionalJump, left, guardValue));
        left.AddInstruction(new(-1, OpCode.ConditionalJump, yes, leftCondition));
        right.AddInstruction(new(-1, OpCode.ConditionalJump, mutation == "inverted" ? no : yes,
            mutation is "inverted" or "wrongPolarity" ? negated : rightCondition));
        Edge(cfg.EntryBlock, head);
        Edge(head, left); Edge(head, right);
        Edge(left, yes); Edge(left, no);
        Edge(right, yes); Edge(right, no);
        Edge(yes, cfg.ExitBlock); Edge(no, cfg.ExitBlock);
        Assert.That(EquivalentBranchFolder.Run(cfg), Is.EqualTo(expected));
        Assert.That(cfg.Blocks.Contains(right), Is.EqualTo(!expected));
        Assert.That(phi.Operands.Count, Is.EqualTo(yes.Predecessors.Count + 1));
        if (expected) Assert.That(phi.Operands[1], Is.EqualTo(new Immediate(7)));
        Assert.That(EquivalentBranchFolder.Run(cfg), Is.False);
    }

    private static LocalVariable Local(string name) => new(name, new Register(null, name));
    private static Block Block(ISILControlFlowGraph cfg, params Instruction[] instructions)
    {
        var block = new Block { ID = cfg.Blocks.Count, Instructions = instructions.ToList() };
        block.CalculateBlockType();
        cfg.Blocks.Add(block);
        return block;
    }
    private static void Edge(Block from, Block to)
    {
        from.Successors.Add(to);
        to.Predecessors.Add(from);
    }
    private static void Fold(ISILControlFlowGraph cfg)
    {
        SsaSimplifier.Run(cfg, []);
        var iterations = 0;
        while (ConstantFolder.Run(cfg) | ConstantBranchFolder.PruneSsa(cfg))
        {
            Assert.That(++iterations, Is.LessThan(100), "folding must converge");
            SsaSimplifier.Run(cfg, []);
        }
        foreach (var block in cfg.Blocks)
        {
            foreach (var successor in block.Successors)
            {
                Assert.That(cfg.Blocks, Does.Contain(successor));
                Assert.That(successor.Predecessors, Does.Contain(block));
            }
            foreach (var phi in block.Instructions.Where(i => i.OpCode == OpCode.Phi))
                Assert.That(phi.Operands.Count, Is.EqualTo(block.Predecessors.Count + 1));
        }
    }

    [TestCase(0, false)]
    [TestCase(1, true)]
    [TestCase(-1, true)]
    public void RemovesOnlyUnreachableSideEffectsAndSelectsTheRightPhiInput(int condition, bool taken)
    {
        var cfg = new ISILControlFlowGraph([]);
        var value = Local("value");
        var phi = new Instruction(-1, OpCode.Phi, value, new Immediate(20), new Immediate(10));
        var ret = new Instruction(-1, OpCode.Return, value);
        var head = Block(cfg);
        var left = Block(cfg, new Instruction(-1, OpCode.CallVoid, new StringLiteral("left")));
        var right = Block(cfg, new Instruction(-1, OpCode.CallVoid, new StringLiteral("right")));
        var merge = Block(cfg, phi, ret);
        head.AddInstruction(new(-1, OpCode.ConditionalJump, right, new Immediate(condition)));
        Edge(cfg.EntryBlock, head);
        Edge(head, left); Edge(head, right);
        // Deliberately reverse predecessor order: phi sources follow edges, not block IDs.
        Edge(right, merge); Edge(left, merge); Edge(merge, cfg.ExitBlock);
        left.AddInstruction(new(-1, OpCode.Jump, merge));
        right.AddInstruction(new(-1, OpCode.Jump, merge));
        Fold(cfg);
        Assert.That(ret.Operands[0], Is.EqualTo(new Immediate(taken ? 20 : 10)));
        Assert.That(cfg.Blocks, Does.Contain(taken ? right : left));
        Assert.That(cfg.Blocks, Does.Not.Contain(taken ? left : right));
        Assert.That(merge.Predecessors, Is.EqualTo(new[] { taken ? right : left }));
    }

    [Test]
    public void KeepsUnknownBranchesAndConflictingPhiInputs()
    {
        var cfg = new ISILControlFlowGraph([]);
        var value = Local("value");
        var head = Block(cfg);
        var left = Block(cfg);
        var right = Block(cfg);
        var phi = new Instruction(-1, OpCode.Phi, value, new Immediate(1), new Immediate(2));
        var merge = Block(cfg, phi, new(-1, OpCode.Return, value));
        head.AddInstruction(new(-1, OpCode.ConditionalJump, right, Local("condition")));
        Edge(cfg.EntryBlock, head); Edge(head, left); Edge(head, right);
        Edge(left, merge); Edge(right, merge); Edge(merge, cfg.ExitBlock);
        left.AddInstruction(new(-1, OpCode.Jump, merge)); right.AddInstruction(new(-1, OpCode.Jump, merge));
        Fold(cfg);
        Assert.That(phi.OpCode, Is.EqualTo(OpCode.Phi));
        Assert.That(head.Successors.Count, Is.EqualTo(2));
    }

    [TestCase("equal", true)]
    [TestCase("self", true)]
    [TestCase("selfOnly", false)]
    [TestCase("different", false)]
    [TestCase("memory", false)]
    [TestCase("local", false)]
    public void FoldsOnlyConstantPhis(string kind, bool folded)
    {
        var value = Local("value");
        IOperand first = kind == "selfOnly" ? value : kind == "memory" ? new MemoryOperand(Local("pointer")) : kind == "local" ? Local("source") : new Immediate(7);
        IOperand second = kind is "self" or "selfOnly" ? value : kind == "different" ? new Immediate(8) : first;
        var phi = new Instruction(0, OpCode.Phi, value, first, second);
        var cfg = new ISILControlFlowGraph([phi, new(1, OpCode.Return, value)]);
        Assert.That(ConstantFolder.Run(cfg), Is.EqualTo(folded));
        Assert.That(phi.OpCode, Is.EqualTo(folded ? OpCode.Move : OpCode.Phi));
    }

    [TestCase("System.Nullable`1", false)]
    [TestCase("System.DateTime", false)]
    [TestCase("System.Int64", true)]
    [TestCase("System.Object", true)]
    public void PreservesAggregateDefaultValuesInsteadOfForwardingScalarZero(string typeName, bool folded)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var type = app.AllTypes.Single(t => t.FullName == typeName);
        if (type.GenericParameters.Count != 0)
            type = type.MakeGenericInstanceType([app.SystemTypes.SystemInt32Type]);
        var value = Local("value");
        value.Type = type;
        var phi = new Instruction(0, OpCode.Phi, value, new Immediate(0), new Immediate(0));
        var cfg = new ISILControlFlowGraph([phi, new(1, OpCode.Return, value)]);
        Assert.That(ConstantFolder.Run(cfg), Is.EqualTo(folded));
        Assert.That(phi.OpCode, Is.EqualTo(folded ? OpCode.Move : OpCode.Phi));
    }

    [Test]
    public void RemovesUnreachableLoopAndItsPhiInputAtReachableJoin()
    {
        var cfg = new ISILControlFlowGraph([]);
        var head = Block(cfg);
        var loop = Block(cfg);
        var value = Local("value");
        var phi = new Instruction(-1, OpCode.Phi, value, new Immediate(3), new Immediate(99));
        var ret = new Instruction(-1, OpCode.Return, value);
        var merge = Block(cfg, phi, ret);
        head.AddInstruction(new(-1, OpCode.ConditionalJump, merge, new Immediate(1)));
        loop.AddInstruction(new(-1, OpCode.CallVoid, new StringLiteral("unreachable")));
        loop.AddInstruction(new(-1, OpCode.ConditionalJump, loop, Local("condition")));
        Edge(cfg.EntryBlock, head); Edge(head, loop); Edge(head, merge);
        Edge(loop, loop); Edge(loop, merge); Edge(merge, cfg.ExitBlock);
        Fold(cfg);
        Assert.That(cfg.Blocks, Does.Not.Contain(loop));
        Assert.That(ret.Operands[0], Is.EqualTo(new Immediate(3)));
        Assert.That(merge.Predecessors, Is.EqualTo(new[] { head }));
    }

    [Test]
    public void RefusesToPruneWhenPhiPredecessorMappingIsMalformed()
    {
        var cfg = new ISILControlFlowGraph([]);
        var head = Block(cfg);
        var value = Local("value");
        var left = Block(cfg, new Instruction(-1, OpCode.Phi, value, new Immediate(1), new Immediate(2)));
        var right = Block(cfg, new Instruction(-1, OpCode.Return));
        head.AddInstruction(new(-1, OpCode.ConditionalJump, right, new Immediate(1)));
        Edge(cfg.EntryBlock, head); Edge(head, left); Edge(head, right);
        Assert.That(ConstantBranchFolder.PruneSsa(cfg), Is.False);
        Assert.That(head.Successors.Count, Is.EqualTo(2));
    }

    [TestCase(0)]
    [TestCase(1)]
    public void LeavesDuplicateSuccessorEdgesUntouched(int condition)
    {
        var cfg = new ISILControlFlowGraph([]);
        var head = Block(cfg);
        var target = Block(cfg, new Instruction(-1, OpCode.Return));
        head.AddInstruction(new(-1, OpCode.ConditionalJump, target, new Immediate(condition)));
        Edge(cfg.EntryBlock, head); Edge(head, target); Edge(head, target);
        Assert.That(ConstantBranchFolder.PruneSsa(cfg), Is.False);
        Assert.That(target.Predecessors.Count, Is.EqualTo(2));
    }

    [Test]
    public void CascadesThroughMoreThanEightDependentJoins()
    {
        var cfg = new ISILControlFlowGraph([]);
        var head = Block(cfg);
        Edge(cfg.EntryBlock, head);
        IOperand condition = new Immediate(1);
        for (var i = 0; i < 12; i++)
        {
            var left = Block(cfg);
            var right = Block(cfg);
            var value = Local("value" + i);
            var phi = new Instruction(-1, OpCode.Phi, value, new Immediate(0), new Immediate(1));
            var merge = Block(cfg, phi);
            head.AddInstruction(new(-1, OpCode.ConditionalJump, right, condition));
            Edge(head, left); Edge(head, right); Edge(left, merge); Edge(right, merge);
            left.AddInstruction(new(-1, OpCode.Jump, merge)); right.AddInstruction(new(-1, OpCode.Jump, merge));
            head = merge;
            condition = value;
        }
        var ret = new Instruction(-1, OpCode.Return, condition);
        head.AddInstruction(ret); Edge(head, cfg.ExitBlock);
        Fold(cfg);
        Assert.That(ret.Operands[0], Is.EqualTo(new Immediate(1)));
        Assert.That(cfg.Instructions.Any(i => i.OpCode is OpCode.Phi or OpCode.ConditionalJump), Is.False);
    }

    [Test]
    public void ResolvesInstructionTargetsAndPreservesExitBlock()
    {
        var ret = new Instruction(3, OpCode.Return, new Immediate(1));
        var branch = new Instruction(0, OpCode.ConditionalJump, ret, new Immediate(1));
        var cfg = new ISILControlFlowGraph([branch, new(1, OpCode.CallVoid, new StringLiteral("unreachable")),
            new(2, OpCode.Return, new Immediate(0)), ret]);
        Fold(cfg);
        Assert.That(cfg.Instructions.Any(i => i.OpCode == OpCode.CallVoid), Is.False);
        Assert.That(cfg.Blocks, Does.Contain(cfg.ExitBlock));
    }
}
