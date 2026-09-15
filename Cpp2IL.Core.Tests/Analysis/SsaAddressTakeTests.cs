using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class SsaAddressTakeTests
{
    private static Register Reg(string name) => new(null, name);

    private static void Build(params Instruction[] instructions)
    {
        var graph = new ISILControlFlowGraph(instructions.ToList());
        SsaForm.Build(graph, new DominatorInfo(graph));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void AddressTakenBeforeStoreUsesStoredVersion(bool multipleStores)
    {
        var take = new Instruction(0, OpCode.Move, Reg("pointer"), new AddressOf(Reg("slot")));
        var first = new Instruction(1, OpCode.Move, Reg("slot"), new Immediate(1));
        var last = new Instruction(2, OpCode.Move, Reg("slot"), new Immediate(2));
        var call = new Instruction(3, OpCode.CallVoid, new StringLiteral("consume"), Reg("pointer"));
        Build(multipleStores ? [take, first, last, call, new(4, OpCode.Return)] : [take, last, call, new(4, OpCode.Return)]);
        Assert.That(((AddressOf)take.Operands[1]).Target, Is.EqualTo(last.Destination));
    }

    [TestCase("read")]
    [TestCase("overwrite")]
    [TestCase("call")]
    [TestCase("arithmetic")]
    public void DoesNotCrossPointerUsesDefinitionsOrNonMoves(string barrier)
    {
        var take = new Instruction(0, OpCode.Move, Reg("pointer"), new AddressOf(Reg("slot")));
        var middle = barrier switch
        {
            "read" => new Instruction(1, OpCode.Move, Reg("copy"), Reg("pointer")),
            "overwrite" => new Instruction(1, OpCode.Move, Reg("pointer"), new Immediate(0)),
            "call" => new Instruction(1, OpCode.CallVoid, new StringLiteral("other")),
            _ => new Instruction(1, OpCode.Add, Reg("sum"), Reg("a"), Reg("b"))
        };
        var store = new Instruction(2, OpCode.Move, Reg("slot"), new Immediate(7));
        Build(take, middle, store, new(3, OpCode.CallVoid, new StringLiteral("consume"), Reg("pointer")), new(4, OpCode.Return));
        Assert.That(((AddressOf)take.Operands[1]).Target, Is.Not.EqualTo(store.Destination));
    }

    [Test]
    public void KeepsBranchTargetAtBlockEntryAfterMovingAddressTake()
    {
        var take = new Instruction(2, OpCode.Move, Reg("pointer"), new AddressOf(Reg("slot")));
        var store = new Instruction(3, OpCode.Move, Reg("slot"), new Immediate(7));
        var jump = new Instruction(0, OpCode.ConditionalJump, take, Reg("condition"));
        Build(jump, new(1, OpCode.Return), take, store,
            new(4, OpCode.CallVoid, new StringLiteral("consume"), Reg("pointer")), new(5, OpCode.Return));
        Assert.That(((Block)jump.Operands[0]).Instructions[0], Is.SameAs(store));
        Assert.That(((AddressOf)take.Operands[1]).Target, Is.EqualTo(store.Destination));
    }
}
