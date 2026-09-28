using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class InitialZeroStoreEliminationTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    // Which of the two zero stores (before and after the operation) survive.
    [TestCase("none", false, false)]
    [TestCase("read", false, true)]
    [TestCase("write", false, true)]
    [TestCase("address", false, true)]
    [TestCase("loop", true, true)]
    [TestCase("notAggregate", true, true)]
    public void ZeroStore_IsDroppedOnlyWhileTheAggregateIsUntouched(string operation, bool firstKept, bool secondKept)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = app.AllTypes.Single(t => t.FullName == "System.Collections.Generic.KeyValuePair`2");
        var instance = new GenericInstanceTypeAnalysisContext(owner, [app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemInt32Type]);
        FieldReference Field(LocalVariable local, string name)
            => new(new ConcreteGenericFieldAnalysisContext(owner.Fields.Single(f => f.Name == name), instance), local, 0);
        var aggregate = new LocalVariable("aggregate", new Register(null, "aggregate_stack_-16"), instance);
        var value = new LocalVariable("value", new Register(null, "value"), app.SystemTypes.SystemInt32Type);

        var first = new Instruction(0, OpCode.Move, Field(aggregate, "key"), new Immediate(0));
        var second = new Instruction(2, OpCode.Move, Field(aggregate, "value"), new Immediate(0));
        var middle = operation switch
        {
            "read" => new Instruction(1, OpCode.Move, value, Field(aggregate, "key")),
            "write" => new Instruction(1, OpCode.Move, Field(aggregate, "key"), value),
            "address" => new Instruction(1, OpCode.Move, value, new AddressOf(aggregate)),
            _ => new Instruction(1, OpCode.Nop),
        };
        List<Instruction> instructions = [first, middle, second];
        // A loop that writes the aggregate after clearing it: the clear runs again on each iteration.
        if (operation == "loop")
            instructions.AddRange([new Instruction(3, OpCode.Move, Field(aggregate, "key"), value), new Instruction(4, OpCode.Jump, first)]);
        instructions.Add(new Instruction(5, OpCode.Return));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
        {
            Locals = [aggregate, value], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph(instructions),
        };
        if (operation != "notAggregate")
            method.StackAggregates[aggregate.Register.Number] = instance;

        InitialZeroStoreElimination.Run(method);

        Assert.That(first.OpCode, Is.EqualTo(firstKept ? OpCode.Move : OpCode.Nop), "first");
        Assert.That(second.OpCode, Is.EqualTo(secondKept ? OpCode.Move : OpCode.Nop), "second");
        Assert.That(middle.OpCode, Is.EqualTo(operation is "read" or "write" or "address" ? OpCode.Move : OpCode.Nop));
    }
}
