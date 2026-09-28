using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class UniTaskAwaiterRecoveryTests
{
    private ApplicationAnalysisContext app = null!;
    private TypeAnalysisContext awaiter = null!;
    private MethodAnalysisContext getStatus = null!, sourceGetResult = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        app = Cpp2IlApi.CurrentAppContext!;
        // The fixture has no UniTask; mirror the members this recovery binds.
        var assembly = new InjectedAssemblyAnalysisContext("UniTask", app);
        var task = new InjectedTypeAnalysisContext(assembly, "Cysharp.Threading.Tasks", "UniTask", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        awaiter = new InjectedTypeAnalysisContext(assembly, "", "Awaiter", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.NestedPublic) { DeclaringType = task };
        awaiter.Methods.Add(new InjectedMethodAnalysisContext(awaiter, "get_IsCompleted", app.SystemTypes.SystemBooleanType, System.Reflection.MethodAttributes.Public, []));
        awaiter.Methods.Add(new InjectedMethodAnalysisContext(awaiter, "GetResult", app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Public, []));
        var source = new InjectedTypeAnalysisContext(assembly, "Cysharp.Threading.Tasks", "IUniTaskSource", null, System.Reflection.TypeAttributes.Interface | System.Reflection.TypeAttributes.Public);
        getStatus = new InjectedMethodAnalysisContext(source, "GetStatus", app.SystemTypes.SystemInt32Type, System.Reflection.MethodAttributes.Public, [app.SystemTypes.SystemInt16Type]);
        sourceGetResult = new InjectedMethodAnalysisContext(source, "GetResult", app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Public, [app.SystemTypes.SystemInt16Type]);
    }

    private LocalVariable Local(string name, TypeAnalysisContext? type) => new(name, new Register(null, name), type);

    private MethodAnalysisContext Method(List<Instruction> instructions, params LocalVariable[] locals)
    {
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "MoveNext", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
        {
            Locals = locals.ToList(), ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph(instructions),
        };
        method.ControlFlowGraph.MergeCallBlocks();
        return method;
    }

    [TestCase(true)]
    [TestCase(false)]
    public void InlinedIsCompleted_CallsTheAwaiterMember(bool fromStorage)
    {
        var slot = Local("stack_-60", awaiter);
        var a = Local("a", awaiter);
        var token = Local("token", app.SystemTypes.SystemInt16Type);
        var isNull = Local("isNull", app.SystemTypes.SystemBooleanType);
        var status = Local("status", app.SystemTypes.SystemInt32Type);
        var pending = Local("pending", app.SystemTypes.SystemBooleanType);
        var join = new Instruction(20, OpCode.Return);
        var suspend = new Instruction(10, OpCode.Return);
        var method = Method(
        [
            new(0, OpCode.Move, a, fromStorage ? slot : token),
            new(1, OpCode.CheckEqual, isNull, a, new Immediate(0)),
            new(2, OpCode.ConditionalJump, join, isNull),
            new(3, OpCode.Call, getStatus, status, a, token),
            new(4, OpCode.CheckEqual, pending, status, new Immediate(0)),
            new(5, OpCode.ConditionalJump, suspend, pending),
            new(6, OpCode.Jump, join),
            suspend,
            join,
        ], slot, a, token, isNull, status, pending);

        Assert.That(UniTaskAwaiterRecovery.Run(method), Is.EqualTo(fromStorage));
        if (!fromStorage)
            return;

        var calls = method.ControlFlowGraph.Blocks.SelectMany(b => b.Instructions).Where(i => i.OpCode == OpCode.Call).ToList();
        Assert.That(calls, Has.Count.EqualTo(1));
        Assert.That(((MethodAnalysisContext)calls[0].Operands[0]).Name, Is.EqualTo("get_IsCompleted"));
        Assert.That(calls[0].Operands[2] is AddressOf { Target: var target } && target == slot, "the awaiter's storage is the receiver");
        var head = method.ControlFlowGraph.Blocks.Single(b => b.Instructions.Contains(calls[0]));
        Assert.That(head.Successors.Select(b => b.Instructions.Contains(join)), Is.EqualTo(new[] { true, false }), "completed goes on, otherwise suspend");
    }

    [Test]
    public void InlinedVoidGetResult_CallsTheAwaiterMember()
    {
        var slot = Local("stack_-60", awaiter);
        var a = Local("a", awaiter);
        var token = Local("token", app.SystemTypes.SystemInt16Type);
        var isNull = Local("isNull", app.SystemTypes.SystemBooleanType);
        var join = new Instruction(20, OpCode.Return);
        var method = Method(
        [
            new(0, OpCode.Move, a, slot),
            new(1, OpCode.CheckEqual, isNull, a, new Immediate(0)),
            new(2, OpCode.ConditionalJump, join, isNull),
            new(3, OpCode.CallVoid, sourceGetResult, a, token),
            new(4, OpCode.Jump, join),
            join,
        ], slot, a, token, isNull);

        Assert.That(UniTaskAwaiterRecovery.Run(method), Is.True);

        var calls = method.ControlFlowGraph.Blocks.SelectMany(b => b.Instructions).Where(i => i.OpCode == OpCode.CallVoid).ToList();
        Assert.That(calls.Select(c => ((MethodAnalysisContext)c.Operands[0]).DeclaringType), Is.EqualTo(new[] { awaiter }));
        Assert.That(method.ControlFlowGraph.Blocks.Single(b => b.Instructions.Contains(join)).Predecessors, Has.Count.EqualTo(1));
    }
}
