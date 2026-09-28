using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class UniTaskBuilderRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    [TestCase("exception", true)]
    [TestCase("otherValue", false)]
    [TestCase("result", true)]
    public void InlinedBuilderCompletion_CallsTheBuilderMember(string shape, bool recovered)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var exception = app.AllTypes.Single(t => t.FullName == "System.Exception");
        // The fixture has no UniTask; mirror the members this recovery binds.
        var assembly = new InjectedAssemblyAnalysisContext("UniTask", app);
        var promiseType = new InjectedTypeAnalysisContext(assembly, "Cysharp.Threading.Tasks.CompilerServices", "IStateMachineRunnerPromise", null, System.Reflection.TypeAttributes.Interface | System.Reflection.TypeAttributes.Public);
        var promiseSetException = new InjectedMethodAnalysisContext(promiseType, "SetException", app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Public, [exception]);
        var promiseSetResult = new InjectedMethodAnalysisContext(promiseType, "SetResult", app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Public, []);
        var builder = new InjectedTypeAnalysisContext(assembly, "Cysharp.Threading.Tasks.CompilerServices", "AsyncUniTaskMethodBuilder", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var runnerPromise = new InjectedFieldAnalysisContext("runnerPromise", promiseType, System.Reflection.FieldAttributes.Private, builder);
        var ex = new InjectedFieldAnalysisContext("ex", exception, System.Reflection.FieldAttributes.Private, builder);
        builder.Methods.Add(new InjectedMethodAnalysisContext(builder, "SetException", app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Public, [exception]));
        builder.Methods.Add(new InjectedMethodAnalysisContext(builder, "SetResult", app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Public, []));
        var machine = new InjectedTypeAnalysisContext(assembly, "", "<Run>d__0", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var builderField = new InjectedFieldAnalysisContext("<>t__builder", builder, System.Reflection.FieldAttributes.Public, machine);

        LocalVariable Local(string name, TypeAnalysisContext type) => new(name, new Register(null, name), type);
        var self = Local("this", machine);
        var promise = Local("promise", promiseType);
        var isNull = Local("isNull", app.SystemTypes.SystemBooleanType);
        var (error, other) = (Local("error", exception), Local("other", exception));
        var join = new Instruction(20, OpCode.Return);
        List<Instruction> instructions =
        [
            new(0, OpCode.Move, promise, new FieldReference(runnerPromise, self, 0, builderField)),
            new(1, OpCode.CheckEqual, isNull, promise, new Immediate(0)),
        ];
        if (shape == "result")
            instructions.AddRange([
                new Instruction(2, OpCode.ConditionalJump, join, isNull),
                new Instruction(3, OpCode.CallVoid, promiseSetResult, promise),
            ]);
        else
        {
            var nullArm = new Instruction(10, OpCode.Move, new FieldReference(ex, self, 8, builderField), shape == "otherValue" ? other : error);
            instructions.AddRange([
                new Instruction(2, OpCode.ConditionalJump, nullArm, isNull),
                new Instruction(3, OpCode.CallVoid, promiseSetException, promise, error),
                new Instruction(4, OpCode.Jump, join),
                nullArm,
            ]);
        }
        instructions.Add(join);
        var method = new InjectedMethodAnalysisContext(machine, "MoveNext", app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Public, [])
        {
            Locals = [self, promise, isNull, error, other], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph(instructions),
        };
        method.ControlFlowGraph.MergeCallBlocks();

        Assert.That(UniTaskBuilderRecovery.Run(method), Is.EqualTo(recovered));
        if (!recovered)
            return;

        var calls = method.ControlFlowGraph.Blocks.SelectMany(b => b.Instructions).Where(i => i.OpCode == OpCode.CallVoid).ToList();
        Assert.That(calls, Has.Count.EqualTo(1));
        Assert.That(((MethodAnalysisContext)calls[0].Operands[0]).DeclaringType, Is.EqualTo(builder));
        Assert.That(calls[0].Operands[1] is AddressOf { Target: FieldReference { Field: var f, IsNested: false } } && f == builderField, "called on the builder field");
        Assert.That(calls[0].Operands.Skip(2), Is.EqualTo(shape == "result" ? System.Array.Empty<IOperand>() : new IOperand[] { error }));
    }
}
