using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class MemberwiseCopyMergingTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    [TestCase(false, true)]
    [TestCase(true, false)]
    public void EveryMemberCopiedFromOneValue_IsTheWholeValueStored(bool valueWrittenBetween, bool merged)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var pairType = app.AllTypes.Single(t => t.FullName == "System.Collections.Generic.KeyValuePair`2");
        var pair = new GenericInstanceTypeAnalysisContext(pairType, [app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemInt32Type]);
        var owner = new InjectedTypeAnalysisContext(new InjectedAssemblyAnalysisContext("Owner", app), "", "Holder", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var field = new InjectedFieldAnalysisContext("pair", pair, System.Reflection.FieldAttributes.Public, owner);
        FieldAnalysisContext Member(string name) => new ConcreteGenericFieldAnalysisContext(pairType.Fields.Single(f => f.Name == name), pair);
        LocalVariable Local(string name, TypeAnalysisContext type) => new(name, new Register(null, name), type);
        var (holder, value, other, key, val) = (Local("holder", owner), Local("value", pair), Local("other", pair),
            Local("key", app.SystemTypes.SystemInt32Type), Local("val", app.SystemTypes.SystemInt32Type));

        List<Instruction> instructions =
        [
            new(0, OpCode.Move, key, new FieldReference(Member("key"), value, 0)),
            new(1, OpCode.Move, val, new FieldReference(Member("value"), value, 4)),
        ];
        if (valueWrittenBetween)
            instructions.Add(new Instruction(2, OpCode.Move, value, other));
        var first = new Instruction(3, OpCode.Move, new FieldReference(Member("key"), holder, 0, field), key);
        instructions.AddRange([first, new Instruction(4, OpCode.Move, new FieldReference(Member("value"), holder, 4, field), val), new Instruction(5, OpCode.Return)]);
        var method = new InjectedMethodAnalysisContext(owner, "Caller", app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Public, [])
        {
            Locals = [holder, value, other, key, val], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph(instructions),
        };

        Assert.That(MemberwiseCopyMerging.Run(method), Is.EqualTo(merged));
        if (!merged)
            return;
        Assert.That(first.Operands[0] is FieldReference { IsNested: false, Field: var f, Local: var l } && f == field && l == holder, "stores the whole field");
        Assert.That(first.Operands[1], Is.EqualTo(value));
    }
}
