using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class DeadCopyCycleTests
{
    [TestCase("none", false)]
    [TestCase("call", true)]
    [TestCase("store", true)]
    [TestCase("address", true)]
    public void RemovesOnlyCyclesWithoutObservableUsers(string use, bool retained)
    {
        var a = new LocalVariable("a", new Register(null, "a"));
        var b = new LocalVariable("b", new Register(null, "b"));
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var phi = new Instruction(0, OpCode.Phi, a, new Immediate(0), b);
        var copy = new Instruction(1, OpCode.Move, b, a);
        var consumer = use switch
        {
            "call" => new Instruction(2, OpCode.CallVoid, new StringLiteral("consume"), b),
            "store" => new Instruction(2, OpCode.Move, new MemoryOperand(pointer), b),
            "address" => new Instruction(2, OpCode.CallVoid, new StringLiteral("consume"), new AddressOf(b)),
            _ => new Instruction(2, OpCode.Nop)
        };
        var cfg = new ISILControlFlowGraph([phi, copy, consumer, new(3, OpCode.Jump, phi)]);
        DeadCodeEliminator.RemoveDeadCopyCycles(cfg);
        Assert.That(phi.OpCode, Is.EqualTo(retained ? OpCode.Phi : OpCode.Nop));
        Assert.That(copy.OpCode, Is.EqualTo(retained ? OpCode.Move : OpCode.Nop));
    }
}
