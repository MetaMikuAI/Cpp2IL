using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Analysis;

public class DelegateInvokeRecoveryTests
{
    private ApplicationAnalysisContext _app = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
        _app.InstructionSet = new NewArmV8InstructionSet();
    }

    private (MethodAnalysisContext Caller, MethodAnalysisContext Invoke, Instruction Dispatch,
        LocalVariable Receiver, IOperand[] Arguments) Create(bool tail, string loadKind, string returnKind = "void", bool floatingParameter = false)
    {
        var returnType = returnKind switch
        {
            "float" => _app.SystemTypes.SystemSingleType,
            "int" => _app.SystemTypes.SystemInt32Type,
            _ => _app.SystemTypes.SystemVoidType
        };
        var multicast = _app.AllTypes.First(t => t.FullName == "System.MulticastDelegate");
        var type = new InjectedTypeAnalysisContext(multicast.DeclaringAssembly, "Tests", "Callback", multicast, TypeAttributes.Public);
        var invoke = type.InjectMethodContext("Invoke", returnType, MethodAttributes.Public,
            floatingParameter ? _app.SystemTypes.SystemSingleType : _app.SystemTypes.SystemStringType);
        var caller = new InjectedMethodAnalysisContext(type, "Caller", returnType, MethodAttributes.Public | MethodAttributes.Static, []);
        var receiver = new LocalVariable("callback", new Register(null, "X8", 0), type);
        var field = _app.AllTypes.First(t => t.FullName == "System.Delegate").Fields.First(f => f.Name == "invoke_impl");
        IOperand load = loadKind switch
        {
            "field" => new FieldReference(field, receiver, field.Offset),
            "nested" => new FieldReference(field.FieldType.Fields.First(f => f.Name == "m_value"), receiver, field.Offset, field),
            _ => new MemoryOperand(receiver, addend: _app.Binary.PointerSizeBytes * 3)
        };
        var target = new LocalVariable("target", new Register(null, "X3", 1));
        var oldResult = new LocalVariable("staleX0", new Register(null, "X0", 1));
        var arguments = _app.InstructionSet.CallingConventionResolver!.ResolveForUnmanaged(_app, 0)
            .Cast<Register>().Select(r => (IOperand)new LocalVariable(r.Name, r.Copy(2))).ToArray();
        var dispatch = new Instruction(1, tail ? OpCode.IndirectJump : OpCode.IndirectCall,
            loadKind == "folded" ? load : target, oldResult);
        dispatch.AddOperands(arguments);
        var instructions = new List<Instruction>();
        if (loadKind != "folded")
            instructions.Add(new Instruction(0, OpCode.Move, target, load));
        instructions.Add(dispatch);
        if (!tail)
            instructions.Add(new Instruction(2, OpCode.Return));
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        caller.Locals.AddRange(new[] { receiver, target, oldResult }.Concat(arguments.Cast<LocalVariable>()));
        return (caller, invoke, dispatch, receiver, arguments);
    }

    [TestCase(false, "raw")]
    [TestCase(false, "field")]
    [TestCase(false, "nested")]
    [TestCase(false, "folded")]
    [TestCase(true, "raw")]
    [TestCase(true, "field")]
    [TestCase(true, "nested")]
    [TestCase(true, "folded")]
    public void RecoversInvokeAndPreservesArguments(bool tail, string loadKind)
    {
        var (caller, invoke, dispatch, receiver, arguments) = Create(tail, loadKind);
        DelegateInvokeRecovery.Run(caller);
        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.CallVoid));
        Assert.That(dispatch.Operands.ToArray(), Is.EqualTo(new IOperand[] { invoke, receiver, arguments[1], arguments[2] }));
        var block = caller.ControlFlowGraph!.Blocks.Single(b => b.Instructions.Contains(dispatch));
        if (tail)
        {
            Assert.That(block.Instructions.Last().OpCode, Is.EqualTo(OpCode.Return));
            Assert.That(block.Instructions.Last().Operands, Is.Empty);
            Assert.That(block.BlockType, Is.EqualTo(BlockType.Return));
        }
        DelegateInvokeRecovery.Run(caller);
        Assert.That(caller.ControlFlowGraph.Instructions.Count(i => i.OpCode == OpCode.Return), Is.EqualTo(1));
    }

    [TestCase("int", "X0")]
    [TestCase("float", "V0")]
    public void TailReturnUsesFreshTypedResult(string returnKind, string register)
    {
        var (caller, invoke, dispatch, _, _) = Create(true, "field", returnKind);
        var staleResult = dispatch.Operands[1];
        DelegateInvokeRecovery.Run(caller);
        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.Call));
        var result = (LocalVariable)dispatch.Operands[1];
        Assert.That(result, Is.Not.SameAs(staleResult));
        Assert.That(result.Type, Is.SameAs(invoke.ReturnType));
        Assert.That(result.Register.Name, Is.EqualTo(register));
        Assert.That(caller.Locals, Does.Contain(result));
        Assert.That(caller.ControlFlowGraph!.Instructions.Last(i => i.OpCode == OpCode.Return).Operands[0], Is.SameAs(result));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void RemapsFloatingArgumentBeforeReplacingReceiver(bool tail)
    {
        var (caller, invoke, dispatch, receiver, arguments) = Create(tail, "field", floatingParameter: true);
        DelegateInvokeRecovery.Run(caller);
        Assert.That(dispatch.Operands.ToArray(), Is.EqualTo(new IOperand[] { invoke, receiver, arguments[8], arguments[1] }));
    }

    [Test]
    public void NormalFloatingReturnKeepsImplicitSsaDefinition()
    {
        var (caller, _, dispatch, _, _) = Create(false, "field", "float");
        var result = new LocalVariable("floatResult", new Register(null, "V0", 3), _app.SystemTypes.SystemSingleType);
        caller.Locals.Add(result);
        dispatch.ImplicitDefinition = result.Register;
        DelegateInvokeRecovery.Run(caller);
        Assert.That(dispatch.Operands[1], Is.SameAs(result));
    }

    [TestCase("System.Action`1", "field")]
    [TestCase("System.Action`1", "nested")]
    [TestCase("System.Func`2", "raw")]
    public void SpecializesConstructedDelegateInvoke(string typeName, string loadKind)
    {
        var (caller, _, dispatch, receiver, arguments) = Create(true, loadKind);
        var definition = _app.AllTypes.First(t => t.FullName == typeName);
        var stringType = _app.SystemTypes.SystemStringType;
        var floatType = _app.SystemTypes.SystemSingleType;
        receiver.Type = definition.MakeGenericInstanceType(typeName == "System.Func`2" ? [stringType, floatType] : [stringType]);
        // Mirror a metadata-backed constructed type: resolution must use GenericType,
        // not depend on BaseType or Methods being populated on the instance.
        receiver.Type.BaseType = _app.SystemTypes.SystemObjectType;
        DelegateInvokeRecovery.Run(caller);
        Assert.That(dispatch.OpCode, Is.EqualTo(typeName == "System.Func`2" ? OpCode.Call : OpCode.CallVoid));
        var invoke = (ConcreteGenericMethodAnalysisContext)dispatch.Operands[0];
        Assert.That(invoke.Parameters[0].ParameterType, Is.SameAs(stringType));
        Assert.That(invoke.DeclaringType, Is.TypeOf<GenericInstanceTypeAnalysisContext>());
        var argumentBase = invoke.IsVoid ? 1 : 2;
        Assert.That(dispatch.Operands[argumentBase], Is.SameAs(receiver));
        Assert.That(dispatch.Operands[argumentBase + 1], Is.SameAs(arguments[1]));
        if (!invoke.IsVoid)
            Assert.That(invoke.ReturnType, Is.SameAs(floatType));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void DoesNotDropStackArguments(bool tail)
    {
        var (caller, invoke, dispatch, _, _) = Create(tail, "field");
        for (var i = 1; i < 8; i++)
            invoke.Parameters.Add(new InjectedParameterAnalysisContext(null, _app.SystemTypes.SystemStringType,
                ParameterAttributes.None, i, invoke));
        var operands = dispatch.Operands.ToArray();
        DelegateInvokeRecovery.Run(caller);
        Assert.That(dispatch.OpCode, Is.EqualTo(tail ? OpCode.IndirectJump : OpCode.IndirectCall));
        Assert.That(dispatch.Operands.ToArray(), Is.EqualTo(operands));
    }

    [Test]
    public void DoesNotInventReturnValueForVoidInvoke()
    {
        var (caller, _, dispatch, _, _) = Create(true, "field");
        caller.ReturnType = _app.SystemTypes.SystemInt32Type;
        DelegateInvokeRecovery.Run(caller);
        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.IndirectJump));
    }

    [Test]
    public void DoesNotPartiallyRewriteMixedResolvedAndUnresolvedTails()
    {
        var (caller, _, dispatch, _, _) = Create(true, "field");
        var unknown = new Instruction(3, OpCode.IndirectJump, new LocalVariable("unknown", new Register(null, "X9")));
        var unknownBlock = new Block { Instructions = [unknown], BlockType = BlockType.TailCall };
        caller.ControlFlowGraph!.Blocks.Add(unknownBlock);
        DelegateInvokeRecovery.Run(caller);
        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.IndirectJump));
        Assert.That(unknown.OpCode, Is.EqualTo(OpCode.IndirectJump));
        Assert.That(caller.ControlFlowGraph.Blocks.SelectMany(b => b.Instructions).Any(i => i.OpCode == OpCode.Return), Is.False);
    }

    [TestCase("offset")]
    [TestCase("index")]
    [TestCase("nonDelegate")]
    [TestCase("otherField")]
    [TestCase("layout")]
    public void LeavesUnprovenDispatchUnchanged(string mismatch)
    {
        var (caller, _, dispatch, receiver, _) = Create(true, "raw");
        var load = caller.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.Move);
        switch (mismatch)
        {
            case "offset": load.SetOperand(1, new MemoryOperand(receiver, addend: 16)); break;
            case "index": load.SetOperand(1, new MemoryOperand(receiver, receiver, 24, 1)); break;
            case "nonDelegate": receiver.Type = _app.SystemTypes.SystemObjectType; break;
            case "otherField":
                var field = _app.AllTypes.First(t => t.FullName == "System.Delegate").Fields.First(f => f.Name == "method_ptr");
                load.SetOperand(1, new FieldReference(field, receiver, field.Offset));
                break;
            case "layout": dispatch.RemoveOperandAt(dispatch.Operands.Count - 1); break;
        }
        var operands = dispatch.Operands.ToArray();
        DelegateInvokeRecovery.Run(caller);
        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.IndirectJump));
        Assert.That(dispatch.Operands.ToArray(), Is.EqualTo(operands));
        Assert.That(caller.ControlFlowGraph.Instructions.Any(i => i.OpCode == OpCode.Return), Is.False);
    }
}
