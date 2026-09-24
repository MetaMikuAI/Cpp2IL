using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class StackReceiverRecoveryTests
{
    private ApplicationAnalysisContext app = null!;
    private static Register Reg(string name) => new(null, name);

    [OneTimeSetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        app = TestGameLoader.LoadSimple2019Game();
    }

    [TestCase("same", true)]
    [TestCase("different", false)]
    [TestCase("call", false)]
    [TestCase("overwrite", false)]
    public void RequiresProvenAddressOnEveryIncomingPath(string kind, bool expected)
    {
        var target = new InjectedMethodAnalysisContext(app.SystemTypes.SystemInt32Type, "Equals",
            app.SystemTypes.SystemBooleanType, MethodAttributes.Public, [app.SystemTypes.SystemInt32Type]);
        var call = new Instruction(8, OpCode.Call, target, Reg("result"), Reg("X0"), new Immediate(0));
        var other = new Instruction(5, OpCode.Move, Reg("X0"), new AddressOf(new StackOffset(kind == "different" ? 16 : 12)));
        var change = kind switch
        {
            "call" => new Instruction(6, OpCode.CallVoid, new Immediate(123)),
            "overwrite" => new Instruction(6, OpCode.Move, Reg("X0"), new Immediate(0)),
            _ => new Instruction(6, OpCode.Nop)
        };
        var store = new Instruction(7, OpCode.Move, new StackOffset(12), Reg("remainder"));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Test",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([
                new(0, OpCode.Move, Reg("X0"), new AddressOf(new StackOffset(12))),
                new(1, OpCode.ConditionalJump, other, Reg("condition")),
                new(2, OpCode.Add, Reg("remainder"), Reg("index"), new Immediate(1)),
                new(3, OpCode.Jump, store), other, change, store, call, new(9, OpCode.Return)
            ])
        };
        StackReceiverRecovery.Run(method);
        Assert.That(call.Operands[2] is AddressOf, Is.EqualTo(expected));
        if (expected) Assert.That(((StackOffset)((AddressOf)call.Operands[2]).Target).Offset, Is.EqualTo(12));
    }
}
