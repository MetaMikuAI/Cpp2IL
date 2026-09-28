using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class OverwrittenMemberStoreEliminationTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    [TestCase(false, true)]
    [TestCase(true, false)]
    public void MemberStore_OverwrittenByTheWholeField_IsDropped(bool readBetween, bool dropped)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var pairType = app.AllTypes.Single(t => t.FullName == "System.Collections.Generic.KeyValuePair`2");
        var pair = new GenericInstanceTypeAnalysisContext(pairType, [app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemInt32Type]);
        var owner = new InjectedTypeAnalysisContext(new InjectedAssemblyAnalysisContext("Owner", app), "", "Owner", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var field = new InjectedFieldAnalysisContext("pair", pair, System.Reflection.FieldAttributes.Private, owner);
        var self = new LocalVariable("this", new Register(null, "this"), owner);
        var (value, whole, read) = (new LocalVariable("value", new Register(null, "value"), app.SystemTypes.SystemInt32Type),
            new LocalVariable("whole", new Register(null, "whole"), pair), new LocalVariable("read", new Register(null, "read"), pair));

        var member = new Instruction(0, OpCode.Move, new FieldReference(new ConcreteGenericFieldAnalysisContext(pairType.Fields.Single(f => f.Name == "value"), pair), self, 4, field), value);
        List<Instruction> instructions = [member];
        if (readBetween)
            instructions.Add(new Instruction(1, OpCode.Move, read, new FieldReference(field, self, 0)));
        instructions.AddRange([new Instruction(2, OpCode.Move, new FieldReference(field, self, 0), whole), new Instruction(3, OpCode.Return)]);
        var method = new InjectedMethodAnalysisContext(owner, "Caller", app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Public, [])
        {
            Locals = [self, value, whole, read], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph(instructions),
        };

        Assert.That(OverwrittenMemberStoreElimination.Run(method), Is.EqualTo(dropped));
        Assert.That(member.OpCode, Is.EqualTo(dropped ? OpCode.Nop : OpCode.Move));
    }
}
