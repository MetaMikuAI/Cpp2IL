using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class SharedTailCallSplitterTests
{
    private static Register Reg(string name) => new(null, name);

    // if (c) { x2 = [x0]; x1 = [x0+8] } else { x2 = [x0+0x10]; x1 = [x0+0x18] }  x0 = x19; br x2
    private static List<Instruction> Build(string shape)
    {
        var list = new List<Instruction>();
        Instruction Add(OpCode opCode, params IOperand[] operands)
        {
            var instruction = new Instruction(list.Count, opCode, operands.ToList());
            list.Add(instruction);
            return instruction;
        }

        if (shape == "hoisted")
            Add(OpCode.Move, Reg("X2"), new MemoryOperand(Reg("X0")));
        var branch = Add(OpCode.ConditionalJump, Reg("X9"), Reg("X9"));
        if (shape != "hoisted")
            Add(OpCode.Move, Reg("X2"), new MemoryOperand(Reg("X0")));
        Add(OpCode.Move, Reg("X1"), new MemoryOperand(Reg("X0"), addend: 8));
        var skip = Add(OpCode.Jump, Reg("X9"));
        var other = shape == "hoisted"
            ? Add(OpCode.Move, Reg("X1"), new MemoryOperand(Reg("X0"), addend: 0x18))
            : Add(OpCode.Move, Reg("X2"), new MemoryOperand(Reg("X0"), addend: 0x10));
        if (shape != "hoisted")
            Add(OpCode.Move, Reg("X1"), new MemoryOperand(Reg("X0"), addend: 0x18));
        var tail = Add(OpCode.Move, Reg("X0"), Reg("X19"));
        switch (shape)
        {
            case "computed":
                Add(OpCode.Add, Reg("X2"), Reg("X2"), Reg("X1"));
                break;
            case "call":
                Add(OpCode.CallVoid, new Immediate(0x1000), Reg("X0"));
                break;
        }
        Add(OpCode.IndirectJump, Reg("X2"));
        branch.SetOperand(0, other);
        skip.SetOperand(0, tail);
        return list;
    }

    [TestCase("split", true)]
    [TestCase("hoisted", false)]
    [TestCase("computed", false)]
    [TestCase("call", false)]
    public void GivesEachLoadedTargetItsOwnTail(string shape, bool split)
    {
        var graph = new ISILControlFlowGraph(Build(shape));
        var tails = graph.Blocks.Count(b => b.Instructions.Count > 0 && b.Instructions[^1].OpCode == OpCode.IndirectJump);
        Assert.That(tails, Is.EqualTo(1));

        Assert.That(SharedTailCallSplitter.Run(graph), Is.EqualTo(split));

        var jumps = graph.Blocks.Where(b => b.Instructions.Count > 0 && b.Instructions[^1].OpCode == OpCode.IndirectJump).ToList();
        Assert.That(jumps, Has.Count.EqualTo(split ? 2 : 1));
        if (!split)
            return;
        foreach (var block in jumps)
        {
            Assert.That(block.Predecessors, Has.Count.EqualTo(1));
            Assert.That(block.Successors, Is.EqualTo(new[] { graph.ExitBlock }));
            // Each copy is reached from a block that loads its own target.
            Assert.That(block.Predecessors[0].Instructions.Any(i => i is { OpCode: OpCode.Move, Operands: [Register { Name: "X2" }, MemoryOperand] }));
        }
        Assert.That(jumps.SelectMany(b => b.Instructions).Distinct().Count(), Is.EqualTo(4), "the copy has its own instructions");
        var jump = graph.Blocks.Single(b => b.Instructions.Count > 0 && b.Instructions[^1].OpCode == OpCode.Jump).Instructions[^1];
        // The jump names its own copy, as a block or as the copy's first instruction.
        Assert.That(jumps.Any(b => (ReferenceEquals(b, jump.Operands[0]) || ReferenceEquals(b.Instructions[0], jump.Operands[0]))
                                   && b.Predecessors[0].Instructions.Contains(jump)));
        Assert.That(graph.ExitBlock.Predecessors.Count(jumps.Contains), Is.EqualTo(2));
    }
}
