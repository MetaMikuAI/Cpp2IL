using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class RedundantTypeCheckFolderTests
{
    private ApplicationAnalysisContext _app = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
    }

    [TestCase("success", true)]
    [TestCase("failure", true)]
    [TestCase("negated", true)]
    [TestCase("instance", true)]
    [TestCase("differentType", false)]
    [TestCase("differentObject", false)]
    [TestCase("join", false)]
    [TestCase("addressed", false)]
    [TestCase("addressedResult", false)]
    [TestCase("addressedCondition", false)]
    public void FoldsOnlyTheProvenTypeTestOutcome(string kind, bool expected)
    {
        var cfg = new ISILControlFlowGraph([]);
        var value = Local("value");
        var first = Local("first");
        var second = Local("second");
        var firstNull = Local("firstNull");
        var secondNull = Local("secondNull");
        var condition = Local("condition");
        var result = Local("result");
        var target = _app.SystemTypes.SystemStringType;
        var guard = Block(cfg, new(-1, OpCode.TryCast, first, target, value),
            new(-1, OpCode.CheckEqual, firstNull, first, new Immediate(0)));
        var other = Block(cfg);
        var checkedBlock = Block(cfg);
        var phi = new Instruction(-1, OpCode.Phi, result, new Immediate(10), new Immediate(20));
        var yes = Block(cfg, phi, new(-1, OpCode.Return, result));
        var no = Block(cfg, new Instruction(-1, OpCode.Return, new Immediate(0)));
        if (kind is "addressedResult" or "addressedCondition")
            guard.AddInstruction(new(-1, OpCode.CallVoid, new StringLiteral("mutate"),
                new AddressOf(kind == "addressedResult" ? first : firstNull)));
        guard.AddInstruction(new(-1, OpCode.ConditionalJump, kind == "failure" ? checkedBlock : other, firstNull));
        if (kind == "addressed")
            checkedBlock.AddInstruction(new(-1, OpCode.CallVoid, new StringLiteral("mutate"), new AddressOf(value)));
        // Stores/calls may mutate object contents but cannot change a captured object's runtime type.
        var effect = new Instruction(-1, OpCode.CallVoid, new StringLiteral("effect"), value);
        checkedBlock.AddInstruction(effect);
        checkedBlock.AddInstruction(new(-1, kind == "instance" ? OpCode.IsInstance : OpCode.TryCast, second,
            kind == "differentType" ? _app.SystemTypes.SystemObjectType : target,
            kind == "differentObject" ? Local("otherObject") : value));
        checkedBlock.AddInstruction(new(-1, OpCode.CheckEqual, secondNull, second, new Immediate(0)));
        if (kind == "negated") checkedBlock.AddInstruction(new(-1, OpCode.Not, condition, secondNull));
        var branch = new Instruction(-1, OpCode.ConditionalJump, yes, kind == "negated" ? condition : secondNull);
        checkedBlock.AddInstruction(branch);
        other.AddInstruction(new(-1, OpCode.Jump, kind == "join" ? checkedBlock : yes));
        Edge(cfg.EntryBlock, guard);
        Edge(guard, checkedBlock); Edge(guard, other);
        Edge(checkedBlock, yes); Edge(checkedBlock, no);
        if (kind == "join")
        {
            Edge(other, checkedBlock);
            phi.RemoveOperandAt(2);
        }
        else Edge(other, yes);
        Edge(yes, cfg.ExitBlock); Edge(no, cfg.ExitBlock);
        Assert.That(RedundantTypeCheckFolder.Run(cfg), Is.EqualTo(expected));
        Assert.That(checkedBlock.Instructions, Does.Contain(effect));
        Assert.That(phi.Operands.Count, Is.EqualTo(yes.Predecessors.Count + 1));
        if (expected)
        {
            Assert.That(branch.OpCode, Is.EqualTo(OpCode.Jump));
            Assert.That(branch.Operands[0], Is.SameAs(kind is "failure" or "negated" ? yes : no));
        }
        else Assert.That(branch.OpCode, Is.EqualTo(OpCode.ConditionalJump));
        Assert.That(RedundantTypeCheckFolder.Run(cfg), Is.False);
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
}
