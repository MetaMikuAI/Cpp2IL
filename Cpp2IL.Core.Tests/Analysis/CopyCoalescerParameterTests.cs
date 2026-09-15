using System.Runtime.CompilerServices;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class CopyCoalescerParameterTests
{
    [TestCase(false)]
    [TestCase(true)]
    public void DoesNotReplaceIncomingParameterWithUninitializedLocal(bool addressTaken)
    {
        var parameter = new LocalVariable("characterId", new Register(null, "X1"));
        var copy = new LocalVariable("copy", new Register(null, "X1", 1));
        var load = new Instruction(0, OpCode.Move, copy, parameter);
        var use = new Instruction(1, OpCode.CallVoid, new StringLiteral("consume"), copy);
        var method = (MethodAnalysisContext)RuntimeHelpers.GetUninitializedObject(typeof(MethodAnalysisContext));
        method.ControlFlowGraph = new ISILControlFlowGraph([load, use,
            addressTaken ? new(2, OpCode.CallVoid, new StringLiteral("escape"), new AddressOf(copy)) : new(2, OpCode.Nop), new(3, OpCode.Return)]);
        method.Locals = [parameter, copy];
        method.ParameterLocals = [parameter];
        CopyCoalescer.Run(method);
        Assert.That(load.OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(load.Operands[1], Is.SameAs(parameter));
        Assert.That(use.Operands[1], Is.SameAs(copy));
    }
}
