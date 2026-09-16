using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class StackFrameAliasTests
{
    private ApplicationAnalysisContext _app = null!;
    private static Register Reg(string name) => new(null, name);

    [OneTimeSetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
    }

    private void Analyze(params Instruction[] instructions)
    {
        var method = new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType, "Frame", _app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph(instructions.ToList()),
            ParameterOperands = []
        };
        StackAnalyzer.Analyze(method);
    }

    [TestCase(false, false)]
    [TestCase(false, true)]
    [TestCase(true, false)]
    [TestCase(true, true)]
    public void ResolvesSpillsBeforeFrameRestore(bool x86, bool extraStackShift)
    {
        var frame = Reg(x86 ? "rbp" : "X29");
        var seed = new Instruction(1, OpCode.Move, frame,
            x86 ? Reg("rsp") : new AddressOf(new StackOffset(32)));
        var store = new Instruction(2, OpCode.Move, new StackOffset(16), Reg("argument"));
        var load = new Instruction(4, OpCode.Move, Reg("result"), new MemoryOperand(frame, addend: x86 ? 16 : -16));
        Analyze(new(0, OpCode.ShiftStack, new Immediate(-64)), seed, store,
            new(3, OpCode.ShiftStack, new Immediate(extraStackShift ? -16 : 0)), load,
            new(5, OpCode.Move, frame, new StackOffset(32)), // epilogue restores old frame pointer
            new(6, OpCode.ShiftStack, new Immediate(extraStackShift ? 80 : 64)), new(7, OpCode.Return));
        Assert.That(load.Operands[1], Is.TypeOf<Register>());
        Assert.That(((Register)load.Operands[1]).Name, Is.EqualTo("stack_-30"));
        Assert.That(load.Operands[1], Is.EqualTo(store.Operands[0]));
    }

    [TestCase("copy", true)]
    [TestCase("restore", false)]
    [TestCase("arithmetic", false)]
    [TestCase("implicit", false)]
    [TestCase("indexed", false)]
    [TestCase("overflow", false)]
    public void RequiresLiveExactAliasAtAccess(string kind, bool expected)
    {
        var frame = Reg("X29");
        var alias = Reg("alias");
        var change = new Instruction(3, OpCode.Move, alias, frame);
        if (kind == "restore") change = new(3, OpCode.Move, frame, new StackOffset(0));
        if (kind == "arithmetic") change = new(3, OpCode.Add, frame, frame, new Immediate(8));
        if (kind == "implicit") change = new(3, OpCode.CallVoid, new Immediate(123)) { ImplicitDefinition = frame };
        var load = new Instruction(4, OpCode.Move, Reg("result"), new MemoryOperand(kind == "copy" ? alias : frame,
            kind == "indexed" ? Reg("index") : null, kind == "overflow" ? long.MaxValue : -16));
        Analyze(new(0, OpCode.ShiftStack, new Immediate(-64)),
            new(1, OpCode.Move, frame, new AddressOf(new StackOffset(32))),
            new(2, OpCode.Move, new StackOffset(16), Reg("argument")), change, load,
            new(5, OpCode.ShiftStack, new Immediate(64)), new(6, OpCode.Return));
        Assert.That(load.Operands[1] is Register, Is.EqualTo(expected));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void RequiresAgreementAcrossBothBranchPaths(bool overwrite)
    {
        var frame = Reg("X29");
        var other = new Instruction(5, OpCode.Nop);
        var load = new Instruction(6, OpCode.Move, Reg("result"), new MemoryOperand(frame, addend: -16));
        Analyze(new(0, OpCode.ShiftStack, new Immediate(-64)),
            new(1, OpCode.Move, frame, new AddressOf(new StackOffset(32))),
            new(2, OpCode.ConditionalJump, other, Reg("condition")),
            new(3, OpCode.Move, frame, overwrite ? new Immediate(0) : frame), new(4, OpCode.Jump, load),
            other, load, new(7, OpCode.ShiftStack, new Immediate(64)), new(8, OpCode.Return));
        Assert.That(load.Operands[1] is Register, Is.EqualTo(!overwrite));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void WaitsForBackEdgeBeforeRewriting(bool overwrite)
    {
        var frame = Reg("X29");
        var load = new Instruction(2, OpCode.Move, Reg("result"), new MemoryOperand(frame, addend: -16));
        var exit = new Instruction(6, OpCode.ShiftStack, new Immediate(64));
        Analyze(new(0, OpCode.ShiftStack, new Immediate(-64)),
            new(1, OpCode.Move, frame, new AddressOf(new StackOffset(32))), load,
            new(3, OpCode.ConditionalJump, exit, Reg("condition")),
            new(4, OpCode.Move, frame, overwrite ? new Immediate(0) : frame),
            new(5, OpCode.Jump, load), exit, new(7, OpCode.Return));
        Assert.That(load.Operands[1] is Register, Is.EqualTo(!overwrite));
    }

    [Test]
    public void LeavesStackLocalPointersForAggregateRecovery()
    {
        var pointer = Reg("X20");
        var load = new Instruction(2, OpCode.Move, Reg("result"), new MemoryOperand(pointer, addend: 8));
        Analyze(new(0, OpCode.ShiftStack, new Immediate(-64)),
            new(1, OpCode.Move, pointer, new AddressOf(new StackOffset(16))), load,
            new(3, OpCode.ShiftStack, new Immediate(64)), new(4, OpCode.Return));
        Assert.That(load.Operands[1], Is.TypeOf<MemoryOperand>());
    }

    [Test]
    public void RejectsOverflowingFrameSeed()
    {
        var frame = Reg("X29");
        var load = new Instruction(2, OpCode.Move, Reg("result"), new MemoryOperand(frame));
        Analyze(new(0, OpCode.ShiftStack, new Immediate(-64)),
            new(1, OpCode.Move, frame, new AddressOf(new StackOffset(int.MinValue))), load,
            new(3, OpCode.ShiftStack, new Immediate(64)), new(4, OpCode.Return));
        Assert.That(load.Operands[1], Is.TypeOf<MemoryOperand>());
    }

    [Test]
    public void DoesNotSeedAnAddressAfterDynamicStackAssignment()
    {
        var frame = Reg("X29");
        var load = new Instruction(2, OpCode.Move, Reg("result"), new MemoryOperand(frame));
        Analyze(new(0, OpCode.Move, Reg("X31"), Reg("dynamic")),
            new(1, OpCode.Move, frame, new AddressOf(new StackOffset(0))), load, new(3, OpCode.Return));
        Assert.That(load.Operands[1], Is.TypeOf<MemoryOperand>());
    }
}
