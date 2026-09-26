using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class CctorGuardFoldTests
{
    private const long Finished = 0xE0;

    // if (!klass->cctor_finished_or_no_cctor) { <initializer, already dropped>; reload; return reload } return cached
    private static (ISILControlFlowGraph Graph, Instruction Branch, Instruction InitEntry) Create(
        bool negated, string mutation = "none")
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var type = app.SystemTypes.SystemStringType;
        var runtimeClass = new RuntimeClassTypeAnalysisContext(type, type.DeclaringAssembly);
        var boolean = app.SystemTypes.SystemBooleanType;
        LocalVariable Local(string name, TypeAnalysisContext? t = null) => new(name, new Register(null, name), t);
        var klass = Local("klass", mutation == "untyped" ? null : runtimeClass);
        var zero = Local("zero", boolean);
        var not = Local("not", boolean);
        var cached = Local("cached");
        var reloaded = Local("reloaded");
        var finishedReturn = new Instruction(30, OpCode.Return, cached);
        var initEntry = new Instruction(10, OpCode.Nop);
        var initReturn = new Instruction(13, OpCode.Return, reloaded);
        // CBZ jumps to the initializer when the flag is zero; CBNZ jumps past it when it is not.
        var branch = new Instruction(3, OpCode.ConditionalJump, negated ? finishedReturn : initEntry, negated ? not : zero);
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, cached, new MemoryOperand(Local("storage"))),
            new(1, OpCode.CheckEqual, zero, new MemoryOperand(klass, addend: mutation == "offset" ? Finished + 4 : Finished), new Immediate(0)),
        };
        if (negated) instructions.Add(new Instruction(2, OpCode.Not, not, zero));
        instructions.Add(branch);
        if (!negated) instructions.Add(finishedReturn);
        instructions.Add(initEntry);
        if (mutation == "unnamedCall") instructions.Add(new Instruction(11, OpCode.CallVoid, new Immediate(0x1234), klass));
        if (mutation == "managedCall")
            instructions.Add(new Instruction(11, OpCode.CallVoid, new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,
                "Managed", app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []), klass));
        instructions.Add(new Instruction(12, OpCode.Move, reloaded, new MemoryOperand(Local("storage2"))));
        instructions.Add(initReturn);
        if (negated) instructions.Add(finishedReturn);
        return (new ISILControlFlowGraph(instructions), branch, initEntry);
    }

    [TestCase(false, "none")]
    [TestCase(true, "none")]
    [TestCase(false, "managedCall")]
    public void TakesTheNotFinishedArm(bool negated, string mutation)
    {
        var (graph, branch, initEntry) = Create(negated, mutation);
        Assert.That(MetadataInitGuardRemover.FoldCctorGuards(graph, Finished), Is.True);
        var taken = (Block)branch.Operands[0];
        var destination = ((Immediate)branch.Operands[1]).Value != 0
            ? taken
            : graph.Blocks.Single(b => b.Instructions.Contains(branch)).Successors.Single(s => s != taken);
        Assert.That(destination.Instructions, Does.Contain(initEntry));
        Assert.That(MetadataInitGuardRemover.FoldCctorGuards(graph, Finished), Is.False);
    }

    [TestCase("offset")]
    [TestCase("untyped")]
    [TestCase("unnamedCall")]
    public void RetainsOtherTests(string mutation)
    {
        var (graph, branch, _) = Create(false, mutation);
        Assert.That(MetadataInitGuardRemover.FoldCctorGuards(graph, Finished), Is.False);
        Assert.That(branch.Operands[1], Is.TypeOf<LocalVariable>());
    }
}
