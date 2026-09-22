using System;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class IteratorCurrentStoreOrderingTests
{
    [TestCase("000c40f9c0035fd6", 24)]
    [TestCase("001440f9c0035fd6", 40)]
    [TestCase("010c40f9c0035fd6", -1)] // different result register
    [TestCase("200c40f9c0035fd6", -1)] // different receiver
    [TestCase("000c40b9c0035fd6", -1)] // 32-bit load
    [TestCase("000c40f91f2003d5", -1)] // additional work, not RET
    [TestCase("000c40f9", -1)]
    public void ProvesOnlyDirectObjectCurrentGetter(string hex, int expected)
        => Assert.That(IteratorCurrentStoreOrdering.DecodeGetter(Convert.FromHexString(hex)),
            Is.EqualTo(expected < 0 ? (int?)null : expected));

    [TestCase("arithmetic", true)]
    [TestCase("fieldRead", true)]
    [TestCase("fieldWrite", true)]
    [TestCase("call", false)]
    [TestCase("divide", false)]
    [TestCase("unknownType", false)]
    [TestCase("alias", false)]
    [TestCase("overlap", false)]
    [TestCase("currentRead", false)]
    [TestCase("state", false)]
    [TestCase("publicField", false)]
    [TestCase("branch", false)]
    [TestCase("redefineValue", false)]
    [TestCase("notThis", false)]
    public void ReordersOnlyIndependentNonthrowingBookkeeping(string shape, bool expected)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var root = app.SystemTypes.SystemObjectType;
        var owner = new InjectedTypeAnalysisContext(root.DeclaringAssembly, "Tests", "Iterator", root, TypeAttributes.Public);
        var current = new InjectedFieldAnalysisContext("value", root, FieldAttributes.Private, owner, 24);
        var number = new InjectedFieldAnalysisContext("number", app.SystemTypes.SystemInt32Type,
            shape == "publicField" ? FieldAttributes.Public : FieldAttributes.Private, owner, shape == "overlap" ? 28 : 32);
        var receiver = new LocalVariable("this", new Register(null, "X0"), owner) { IsThis = shape != "notThis" };
        var alias = new LocalVariable("alias", new Register(null, "X1"), owner);
        var x = new LocalVariable("x", new Register(null, "X2"), app.SystemTypes.SystemInt32Type);
        var y = new LocalVariable("y", new Register(null, "X3"), shape == "unknownType" ? null : app.SystemTypes.SystemInt32Type);
        var yielded = new LocalVariable("yielded", new Register(null, "X4"), root);
        IOperand value = shape == "redefineValue" ? yielded : new Immediate(0);
        var first = new Instruction(0, OpCode.Move, new FieldReference(current, receiver, 24), value) { NativeAddress = 0x1000 };
        var field = new FieldReference(number, shape == "alias" ? alias : receiver, number.Offset);
        var next = shape switch
        {
            "call" => new Instruction(1, OpCode.CallVoid, new Immediate(123)),
            "branch" => new Instruction(1, OpCode.Jump, new Instruction(3, OpCode.Return)),
            "divide" => new Instruction(1, OpCode.Divide, y, x, new Immediate(0)),
            "fieldRead" or "alias" or "overlap" or "publicField" => new Instruction(1, OpCode.Move, y, field),
            "fieldWrite" => new Instruction(1, OpCode.Move, field, x),
            "state" => new Instruction(1, OpCode.Move, field, new Immediate(1)),
            "currentRead" => new Instruction(1, OpCode.Move, yielded, new FieldReference(current, receiver, 24)),
            "redefineValue" => new Instruction(1, OpCode.Move, yielded, new Immediate(0)),
            _ => new Instruction(1, OpCode.Add, y, x, new Immediate(1))
        };
        next.NativeAddress = 0x1004;
        var block = new Block { Instructions = [first, next] };
        var originalOperation = next.OpCode;
        IteratorCurrentStoreOrdering.Order(block, current);
        Assert.That(block.Instructions[0], Is.SameAs(first), "Preserve incoming branch target identity");
        Assert.That(first.NativeAddress, Is.EqualTo(expected ? 0x1004UL : 0x1000UL));
        Assert.That(first.OpCode, Is.EqualTo(expected ? originalOperation : OpCode.Move));
        Assert.That(expected ? next.Operands[0] : first.Operands[0], Is.TypeOf<FieldReference>());
        Assert.That(((FieldReference)(expected ? next.Operands[0] : first.Operands[0])).Field, Is.SameAs(current));
    }
}
