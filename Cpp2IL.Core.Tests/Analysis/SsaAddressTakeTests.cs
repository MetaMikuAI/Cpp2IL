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

    [TestCase("barrier", true)]
    [TestCase("unknown", false)]
    [TestCase("copy", false)]
    [TestCase("store", false)]
    [TestCase("pointerAddress", false)]
    [TestCase("secondCall", false)]
    [TestCase("noProof", false)]
    [TestCase("unlifted", false)]
    public void ReadOnlyBarrierAddressDoesNotInventANewSlotValue(string use, bool preserved)
    {
        var store = new Instruction(0, OpCode.Move, Reg("slot"), new Immediate(7));
        var take = new Instruction(1, OpCode.Move, Reg("X0"), new AddressOf(Reg("slot")));
        var call = new Instruction(2, OpCode.Call, new Immediate(use == "unknown" ? 0x2000 : 0x1000), Reg("X0"), Reg("X0"));
        var middle = use switch
        {
            "unlifted" => new Instruction(3, OpCode.NotImplemented, new StringLiteral("unknown native effects")),
            "copy" => new Instruction(3, OpCode.Move, Reg("alias"), Reg("X0")),
            "store" => new Instruction(3, OpCode.Move, new MemoryOperand(Reg("X0")), new Immediate(0)),
            "pointerAddress" => new Instruction(3, OpCode.Move, Reg("alias"), new AddressOf(Reg("X0"))),
            "secondCall" => new Instruction(3, OpCode.Call, new Immediate(0x2000), Reg("X0"), Reg("X0")),
            _ => new Instruction(3, OpCode.Nop)
        };
        var consumeAlias = use == "pointerAddress"
            ? new Instruction(4, OpCode.CallVoid, new StringLiteral("consume"), Reg("alias"))
            : new Instruction(4, OpCode.Nop);
        var returned = new Instruction(6, OpCode.Return, Reg("slot"));
        var graph = new ISILControlFlowGraph([store, take, call, middle,
            consumeAlias, new(5, OpCode.Move, Reg("X0"), new Immediate(0)), returned]);
        SsaForm.Build(graph, new DominatorInfo(graph), writeBarrier: use == "noProof" ? 0UL : 0x1000UL);
        Assert.That(returned.Operands[0].Equals(store.Destination), Is.EqualTo(preserved));
        Assert.That(((AddressOf)take.Operands[1]).Target.Equals(store.Destination), Is.EqualTo(preserved));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void ChecksBothSuccessorPathsForBarrierPointerEscapes(bool escapes)
    {
        var store = new Instruction(0, OpCode.Move, Reg("slot"), new Immediate(7));
        var take = new Instruction(1, OpCode.Move, Reg("X0"), new AddressOf(Reg("slot")));
        var returned = new Instruction(7, OpCode.Return, Reg("slot"));
        var other = escapes
            ? new Instruction(6, OpCode.Call, new Immediate(0x2000), Reg("X0"), Reg("X0"))
            : new Instruction(6, OpCode.Move, Reg("X0"), new Immediate(0));
        var graph = new ISILControlFlowGraph([store, take,
            new(2, OpCode.Call, new Immediate(0x1000), Reg("X0"), Reg("X0")),
            new(3, OpCode.ConditionalJump, other, Reg("condition")),
            new(4, OpCode.Move, Reg("X0"), new Immediate(0)), new(5, OpCode.Jump, returned), other, returned]);
        SsaForm.Build(graph, new DominatorInfo(graph), writeBarrier: 0x1000);
        Assert.That(returned.Operands[0].Equals(store.Destination), Is.EqualTo(!escapes));
    }
}
