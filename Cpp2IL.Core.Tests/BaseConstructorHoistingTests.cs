using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class BaseConstructorHoistingTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    [TestCase(false, true)]
    [TestCase(true, false)]
    public void ObjectConstructorAfterInitializers_RunsFirst(bool thisPassedBefore, bool hoisted)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(new InjectedAssemblyAnalysisContext("Owner", app), "", "Owner", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var field = new InjectedFieldAnalysisContext("count", app.SystemTypes.SystemInt32Type, System.Reflection.FieldAttributes.Private, owner);
        var objectConstructor = app.SystemTypes.SystemObjectType.Methods.Single(m => m.Name == ".ctor");
        var helper = new InjectedMethodAnalysisContext(owner, "Register", app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [owner]);
        var self = new LocalVariable("this", new Register(null, "this"), owner) { IsThis = true };

        var baseCall = new Instruction(2, OpCode.CallVoid, objectConstructor, self);
        List<Instruction> instructions = [new(0, OpCode.Move, new FieldReference(field, self, 16), new Immediate(1))];
        if (thisPassedBefore)
            instructions.Add(new Instruction(1, OpCode.CallVoid, helper, self));
        instructions.AddRange([baseCall, new Instruction(3, OpCode.Return)]);
        var method = new InjectedMethodAnalysisContext(owner, ".ctor", app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Public, [])
        {
            Locals = [self], ParameterLocals = [self],
            ControlFlowGraph = new ISILControlFlowGraph(instructions),
        };
        method.ControlFlowGraph.MergeCallBlocks();

        Assert.That(BaseConstructorHoisting.Run(method), Is.EqualTo(hoisted));
        Assert.That(method.ControlFlowGraph.Instructions.First(i => i.OpCode != OpCode.Nop) == baseCall, Is.EqualTo(hoisted));
    }
}
