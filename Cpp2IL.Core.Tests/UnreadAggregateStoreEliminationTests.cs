using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class UnreadAggregateStoreEliminationTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    [TestCase("none", true)]
    [TestCase("read", false)]
    [TestCase("address", false)]
    [TestCase("whole", false)]
    public void StoresToAnAggregateNothingReads_AreDropped(string use, bool dropped)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = app.AllTypes.Single(t => t.FullName == "System.Collections.Generic.KeyValuePair`2");
        var pair = new GenericInstanceTypeAnalysisContext(owner, [app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemInt32Type]);
        FieldReference Field(LocalVariable local, string name) => new(new ConcreteGenericFieldAnalysisContext(owner.Fields.Single(f => f.Name == name), pair), local, 0);
        var slot = new LocalVariable("slot", new Register(null, "stack_-16"), pair);
        var (value, other) = (new LocalVariable("value", new Register(null, "value"), app.SystemTypes.SystemInt32Type), new LocalVariable("other", new Register(null, "other"), pair));
        var store = new Instruction(0, OpCode.Move, Field(slot, "key"), value);
        List<Instruction> instructions = [store];
        instructions.Add(use switch
        {
            "read" => new Instruction(1, OpCode.Move, value, Field(slot, "value")),
            "address" => new Instruction(1, OpCode.Move, other, new AddressOf(slot)),
            "whole" => new Instruction(1, OpCode.Move, other, slot),
            _ => new Instruction(1, OpCode.Nop),
        });
        instructions.Add(new Instruction(2, OpCode.Return));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
        {
            Locals = [slot, value, other], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph(instructions),
        };
        method.StackAggregates[slot.Register.Number] = pair;

        Assert.That(UnreadAggregateStoreElimination.Run(method), Is.EqualTo(dropped));
        Assert.That(store.OpCode, Is.EqualTo(dropped ? OpCode.Nop : OpCode.Move));
    }
}
