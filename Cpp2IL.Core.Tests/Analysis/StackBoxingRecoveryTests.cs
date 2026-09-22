using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class StackBoxingRecoveryTests
{
    private ApplicationAnalysisContext _app = null!;
    private TypeAnalysisContext _enum = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
        _enum = _app.AllTypes.First(t => t.IsEnumType && t.EnumUnderlyingType == _app.SystemTypes.SystemInt32Type);
    }

    private (MethodAnalysisContext Method, Instruction Call, Instruction Header, Instruction Monitor, Instruction Payload) Create(bool branch)
    {
        var target = _app.SystemTypes.EnumType.Methods.Single(m => m.Name == "ToString" && m.Parameters.Count == 0);
        var receiver = new Register(null, "X0");
        var result = new Register(null, "result");
        var header = new Instruction(10, OpCode.Move, new StackOffset(-32, 8), _enum);
        var monitor = new Instruction(11, OpCode.Move, new StackOffset(-24, 8), new Immediate(-1));
        var payload = new Instruction(1, OpCode.Move, new StackOffset(-16, 4), new Immediate(0));
        var call = new Instruction(13, OpCode.Call, target, result, receiver);
        var instructions = new System.Collections.Generic.List<Instruction>();
        if (branch)
        {
            var other = new Instruction(4, OpCode.Move, new StackOffset(-16, 4), new Immediate(1));
            instructions.Add(new(0, OpCode.ConditionalJump, other, new Register(null, "condition")));
            instructions.Add(payload);
            instructions.Add(new(2, OpCode.Jump, header));
            instructions.Add(other);
        }
        else instructions.Add(payload);
        instructions.AddRange([header, monitor, new(12, OpCode.Move, receiver, new AddressOf(new StackOffset(-32))), call, new(14, OpCode.Return, result)]);
        var method = new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType, "Format", _app.SystemTypes.SystemStringType,
            MethodAttributes.Public | MethodAttributes.Static, []) { ControlFlowGraph = new ISILControlFlowGraph(instructions) };
        return (method, call, header, monitor, payload);
    }

    [TestCase(false)]
    [TestCase(true)]
    public void PreservesPayloadAndBranchValuesThroughSsaAndDeadCodeElimination(bool branch)
    {
        var (method, call, _, _, _) = Create(branch);
        StackAnalyzer.Analyze(method);
        method.DominatorInfo = new DominatorInfo(method.ControlFlowGraph!);
        SsaForm.Build(method);
        LocalVariables.CreateAll(method);
        DeadCodeEliminator.Run(method);
        var box = method.ControlFlowGraph!.Instructions.Single(i => i.OpCode == OpCode.Box);
        Assert.That(box.Operands[1], Is.SameAs(_enum));
        Assert.That(call.Operands[2], Is.SameAs(box.Destination));
        LocalVariables.ResolveTypesAndFields(method);
        var value = (LocalVariable)((AddressOf)box.Operands[2]).Target;
        Assert.That(value.Type, Is.SameAs(_enum));
        var definition = method.ControlFlowGraph.Instructions.Single(i => ReferenceEquals(i.Destination, value));
        if (branch)
        {
            Assert.That(definition.OpCode, Is.EqualTo(OpCode.Phi));
            var values = definition.Operands.Skip(1).Select(local => method.ControlFlowGraph.Instructions
                .Single(i => ReferenceEquals(i.Destination, local)).Operands[1]).Cast<Immediate>().Select(i => i.Value);
            Assert.That(values, Is.EquivalentTo(new long[] { 0, 1 }));
        }
        else Assert.That(definition.Operands[1], Is.EqualTo(new Immediate(0)));
    }

    [TestCase("monitor")]
    [TestCase("headerType")]
    [TestCase("headerWidth")]
    [TestCase("payloadWidth")]
    [TestCase("missingPath")]
    [TestCase("call")]
    [TestCase("indirectCall")]
    [TestCase("unknownWrite")]
    [TestCase("partialOverwrite")]
    [TestCase("otherMethod")]
    [TestCase("unboxedAddress")]
    [TestCase("classDereference")]
    public void RequiresCompleteObjectAndNonEscapingConsumer(string problem)
    {
        var (method, call, header, monitor, payload) = Create(branch: true);
        var block = method.ControlFlowGraph!.Blocks.Single(b => b.Instructions.Contains(call));
        switch (problem)
        {
            case "classDereference":
                var typeRegister = new Register(null, "X8");
                block.Instructions.Insert(0, new(8, OpCode.Move, typeRegister, _enum));
                header.SetOperand(1, new MemoryOperand(typeRegister, accessSize: 8));
                break;
            case "monitor": monitor.SetOperand(1, new Immediate(0)); break;
            case "headerType": header.SetOperand(1, _app.SystemTypes.SystemInt32Type); break;
            case "headerWidth": header.SetOperand(0, new StackOffset(-32, 4)); break;
            case "payloadWidth": payload.SetOperand(0, new StackOffset(-16, 8)); break;
            case "missingPath": payload.OpCode = OpCode.Nop; payload.SetOperands(); break;
            case "indirectCall": block.Instructions.Insert(0, new(9, OpCode.IndirectCall, new Register(null, "callee"), new Register(null, "result"))); break;
            case "call": block.Instructions.Insert(0, new(9, OpCode.CallVoid, new Immediate(123))); break;
            case "unknownWrite": block.Instructions.Insert(0, new(9, OpCode.Move, new MemoryOperand(new Register(null, "pointer")), new Immediate(0))); break;
            case "partialOverwrite": block.Instructions.Insert(0, new(9, OpCode.Move, new StackOffset(-15, 1), new Immediate(0))); break;
            case "otherMethod": call.SetOperand(0, _app.SystemTypes.EnumType.Methods.Single(m => m.Name == "GetHashCode")); break;
            case "unboxedAddress": call.SetOperand(2, new AddressOf(new StackOffset(-16))); break;
        }
        StackBoxingRecovery.Run(method);
        Assert.That(method.ControlFlowGraph.Instructions.Any(i => i.OpCode == OpCode.Box), Is.False);
    }

    [TestCase(false)]
    [TestCase(true)]
    public void RequiresUnanimousHeaderRegisterCopiesAcrossBothPredecessors(bool conflicting)
    {
        var (method, _, header, monitor, _) = Create(branch: true);
        var join = method.ControlFlowGraph!.Blocks.Single(b => b.Instructions.Contains(header));
        var typeRegister = new Register(null, "X8");
        var monitorRegister = new Register(null, "X9");
        var first = true;
        foreach (var predecessor in join.Predecessors)
        {
            var at = predecessor.Instructions.Count;
            if (!predecessor.Instructions[^1].IsFallThrough) at--;
            predecessor.Instructions.Insert(at++, new(20, OpCode.Move, typeRegister,
                conflicting && !first ? _app.SystemTypes.SystemInt32Type : _enum));
            first = false;
            predecessor.Instructions.Insert(at, new(21, OpCode.Move, monitorRegister, new Immediate(-1)));
        }
        header.SetOperand(1, typeRegister);
        monitor.SetOperand(1, monitorRegister);
        StackBoxingRecovery.Run(method);
        Assert.That(method.ControlFlowGraph.Instructions.Count(i => i.OpCode == OpCode.Box), Is.EqualTo(conflicting ? 0 : 1));
    }
}
