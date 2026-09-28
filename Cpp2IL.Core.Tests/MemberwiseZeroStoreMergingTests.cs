using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class MemberwiseZeroStoreMergingTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    [TestCase("all", true)]
    [TestCase("some", false)]
    [TestCase("readBetween", false)]
    [TestCase("twice", false)]
    public void ZeroStoresClearingEveryMember_BecomeOneWholeFieldStore(string shape, bool merged)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var pairType = app.AllTypes.Single(t => t.FullName == "System.Collections.Generic.KeyValuePair`2");
        var pair = new GenericInstanceTypeAnalysisContext(pairType, [app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemInt32Type]);
        var assembly = new InjectedAssemblyAnalysisContext("Owner", app);
        var owner = new InjectedTypeAnalysisContext(assembly, "", "Owner", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var field = new InjectedFieldAnalysisContext("pair", pair, System.Reflection.FieldAttributes.Private, owner);
        FieldReference Member(LocalVariable local, string name)
            => new(new ConcreteGenericFieldAnalysisContext(pairType.Fields.Single(f => f.Name == name), pair), local, 0, field);
        var self = new LocalVariable("this", new Register(null, "this"), owner);
        var read = new LocalVariable("read", new Register(null, "read"), app.SystemTypes.SystemInt32Type);

        var key = new Instruction(0, OpCode.Move, Member(self, "key"), new Immediate(0));
        List<Instruction> instructions = [key];
        if (shape == "readBetween")
            instructions.Add(new Instruction(1, OpCode.Move, read, Member(self, "key")));
        if (shape == "twice")
            instructions.Add(new Instruction(1, OpCode.Move, Member(self, "key"), new Immediate(0)));
        if (shape != "some")
            instructions.Add(new Instruction(2, OpCode.Move, Member(self, "value"), new Immediate(0)));
        instructions.Add(new Instruction(3, OpCode.Return));
        var method = new InjectedMethodAnalysisContext(owner, "Caller", app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Public, [])
        {
            Locals = [self, read], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph(instructions),
        };

        Assert.That(MemberwiseZeroStoreMerging.Run(method), Is.EqualTo(merged));

        var stores = method.ControlFlowGraph.Blocks.SelectMany(b => b.Instructions).Where(i => i.OpCode == OpCode.Move).ToList();
        if (!merged)
        {
            Assert.That(stores.All(s => s.Operands[0] is not FieldReference { IsNested: false }));
            return;
        }
        var whole = (FieldReference)stores.Single().Operands[0];
        Assert.That((whole.Field, whole.Local, whole.IsNested), Is.EqualTo((field, self, false)));
        Assert.That(whole.AccessSize, Is.EqualTo(8));
    }
}
