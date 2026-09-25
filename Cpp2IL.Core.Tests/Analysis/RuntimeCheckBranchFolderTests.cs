using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class RuntimeCheckBranchFolderTests
{
    private ApplicationAnalysisContext _app = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
    }

    private static RuntimeClassTypeAnalysisContext Class(TypeAnalysisContext type) => new(type, type.DeclaringAssembly);

    // condition; ConditionalJump @join, flag; arm; Jump @join; join: Return
    private static (ISILControlFlowGraph Graph, Instruction Branch) Guard(List<Instruction> condition, LocalVariable flag, params Instruction[] arm)
    {
        var instructions = new List<Instruction>(condition);
        var branch = new Instruction(instructions.Count, OpCode.ConditionalJump, new Immediate(0), flag);
        instructions.Add(branch);
        foreach (var instruction in arm)
            instructions.Add(new Instruction(instructions.Count, instruction.OpCode, instruction.Operands.ToList()));
        var jump = new Instruction(instructions.Count, OpCode.Jump, new Immediate(0));
        instructions.Add(jump);
        var join = new Instruction(instructions.Count, OpCode.Return);
        instructions.Add(join);
        branch.SetOperand(0, join);
        jump.SetOperand(0, join);
        return (new ISILControlFlowGraph(instructions), branch);
    }

    private static Block BlockOf(ISILControlFlowGraph graph, Instruction instruction) =>
        graph.Blocks.Single(b => b.Instructions.Contains(instruction));

    [Test]
    public void FoldsEmptyClassInitGuard()
    {
        var klass = new LocalVariable("klass", new Register(null, "X0"), Class(_app.SystemTypes.SystemObjectType));
        var flag = new LocalVariable("flag", new Register(null, "TEMP"));
        var (graph, branch) = Guard([
            new(0, OpCode.Move, klass, Class(_app.SystemTypes.SystemObjectType)),
            new(1, OpCode.CheckEqual, flag, new MemoryOperand(klass, addend: 0xE0), new Immediate(0))], flag);
        var guard = BlockOf(graph, branch);
        var blocks = graph.Blocks.Count;

        Assert.That(RuntimeCheckBranchFolder.Run(graph), Is.True);
        Assert.That(branch.OpCode, Is.EqualTo(OpCode.Jump));
        Assert.That(guard.Successors.Single().Instructions.Single().OpCode, Is.EqualTo(OpCode.Return));
        Assert.That(graph.Blocks, Has.Count.EqualTo(blocks - 1), "the empty arm is unreachable and removed");
    }

    [Test]
    public void FoldsEmptyRepeatedTypeCheck()
    {
        var value = new LocalVariable("value", new Register(null, "X1"), _app.SystemTypes.SystemObjectType);
        var isInstance = new LocalVariable("isInstance", new Register(null, "ISINSTANCE"), _app.SystemTypes.SystemBooleanType);
        var flag = new LocalVariable("flag", new Register(null, "TEMP"));
        var (graph, _) = Guard([
            new(0, OpCode.IsInstance, isInstance, _app.SystemTypes.SystemStringType, value),
            new(1, OpCode.CheckEqual, flag, isInstance, new Immediate(0))], flag);

        Assert.That(RuntimeCheckBranchFolder.Run(graph), Is.True);
    }

    [Test]
    public void FoldsEmptyExactTypeCheck()
    {
        var value = new LocalVariable("value", new Register(null, "X1"), _app.SystemTypes.SystemObjectType);
        var header = new LocalVariable("header", new Register(null, "X8"));
        var flag = new LocalVariable("flag", new Register(null, "TEMP"));
        var (graph, _) = Guard([
            new(0, OpCode.Move, header, new MemoryOperand(value)),
            new(1, OpCode.CheckNotEqual, flag, header, Class(_app.SystemTypes.SystemStringType))], flag);

        Assert.That(RuntimeCheckBranchFolder.Run(graph), Is.True);
    }

    [Test]
    public void KeepsBranchOnProgramData()
    {
        // An empty branch on a parameter means its arms lost their values; it has to stay visible.
        var parameter = new LocalVariable("active", new Register(null, "X1"), _app.SystemTypes.SystemBooleanType);
        var flag = new LocalVariable("flag", new Register(null, "TEMP"));
        var (graph, branch) = Guard([new(0, OpCode.CheckEqual, flag, parameter, new Immediate(0))], flag);

        Assert.That(RuntimeCheckBranchFolder.Run(graph), Is.False);
        Assert.That(branch.OpCode, Is.EqualTo(OpCode.ConditionalJump));
    }

    [Test]
    public void KeepsGuardWhoseArmStillDoesSomething()
    {
        var klass = new LocalVariable("klass", new Register(null, "X0"), Class(_app.SystemTypes.SystemObjectType));
        var flag = new LocalVariable("flag", new Register(null, "TEMP"));
        var (graph, _) = Guard([
                new(0, OpCode.Move, klass, Class(_app.SystemTypes.SystemObjectType)),
                new(1, OpCode.CheckEqual, flag, new MemoryOperand(klass, addend: 0xE0), new Immediate(0))], flag,
            new Instruction(0, OpCode.Call, new Immediate(0x1234), klass));

        Assert.That(RuntimeCheckBranchFolder.Run(graph), Is.False);
    }

    [Test]
    public void KeepsConditionOnMultiplyAssignedLocal()
    {
        // Out of SSA a local assigned twice has no single meaning to prove the condition from.
        var value = new LocalVariable("value", new Register(null, "X1"), _app.SystemTypes.SystemObjectType);
        var isInstance = new LocalVariable("isInstance", new Register(null, "ISINSTANCE"), _app.SystemTypes.SystemBooleanType);
        var flag = new LocalVariable("flag", new Register(null, "TEMP"));
        var (graph, _) = Guard([
            new(0, OpCode.IsInstance, isInstance, _app.SystemTypes.SystemStringType, value),
            new(1, OpCode.Move, isInstance, value),
            new(2, OpCode.CheckEqual, flag, isInstance, new Immediate(0))], flag);

        Assert.That(RuntimeCheckBranchFolder.Run(graph), Is.False);
    }
}
