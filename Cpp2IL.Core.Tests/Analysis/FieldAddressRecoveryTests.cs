using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class FieldAddressRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [TestCase(false, false, false)]
    [TestCase(false, true, false)]
    [TestCase(true, false, false)]
    [TestCase(true, true, false)]
    [TestCase(false, false, true)]
    [TestCase(false, true, true)]
    [TestCase(true, false, true)]
    [TestCase(true, true, true)]
    public void RecoversFieldReceiverAndRefArgument(bool byRefArgument, bool reversed, bool valueOwner)
    {
        var (method, call, receiver, field) = Create(byRefArgument, reversed, valueOwner);
        FieldAddressRecovery.Run(method);
        Assert.That(call.Operands[1], Is.TypeOf<AddressOf>());
        var recovered = (FieldReference)((AddressOf)call.Operands[1]).Target;
        Assert.That(recovered.Field, Is.SameAs(field));
        Assert.That(recovered.Local, Is.SameAs(receiver));
        Assert.That(DeadCodeEliminator.UsedLocals(call), Does.Contain(receiver));
        FieldAddressRecovery.Run(method);
        DeadCodeEliminator.Run(method);
        Assert.That(method.ControlFlowGraph!.Instructions.Any(i => i.OpCode == OpCode.Add), Is.False);
        Assert.That(method.ControlFlowGraph.Instructions, Does.Contain(call));
    }

    [TestCase("offset")]
    [TestCase("type")]
    [TestCase("static")]
    [TestCase("ambiguous")]
    [TestCase("mutable")]
    [TestCase("receiverWrite")]
    [TestCase("definitions")]
    public void RejectsUnprovenFieldAddresses(string reason)
    {
        var (method, call, receiver, field) = Create(false, false);
        var block = method.ControlFlowGraph!.Blocks.Single(b => b.Instructions.Contains(call));
        switch (reason)
        {
            case "offset": field.Offset = 12; break;
            case "type": field.FieldType = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt64Type; break;
            case "static": field.Attributes |= FieldAttributes.Static; break;
            case "ambiguous": field.DeclaringType!.Fields.Add(new InjectedFieldAnalysisContext("Alias", field.FieldType,
                FieldAttributes.Public, field.DeclaringType, field.Offset)); break;
            case "mutable": receiver.IsThis = false; break;
            case "receiverWrite": block.Instructions.Insert(0, new Instruction(9, OpCode.Move, receiver, new Immediate(0))); break;
            case "definitions": block.Instructions.Insert(0, new Instruction(9, OpCode.Move, call.Operands[1], new Immediate(0))); break;
        }
        FieldAddressRecovery.Run(method);
        Assert.That(call.Operands[1], Is.TypeOf<LocalVariable>());
    }

    [TestCase(true)]
    [TestCase(false)]
    public void OnlyProvenStableStackStorageCanSupplyAnInteriorFieldAddress(bool registeredStorage)
    {
        var (method, call, receiver, field) = Create(false, false, true);
        receiver.IsThis = false;
        if (registeredStorage) method.StackAggregates.Add(receiver.Register.Number, receiver.Type!);
        var address = method.ControlFlowGraph!.Instructions.Single(i => i.OpCode == OpCode.Add);
        address.SetOperand(1, new AddressOf(receiver));
        FieldAddressRecovery.Run(method);
        if (registeredStorage)
        {
            var recovered = (FieldReference)((AddressOf)call.Operands[1]).Target;
            Assert.That(recovered.Local, Is.SameAs(receiver));
            Assert.That(recovered.Field, Is.SameAs(field));
        }
        else Assert.That(call.Operands[1], Is.TypeOf<LocalVariable>());
    }

    private static (MethodAnalysisContext, Instruction, LocalVariable, FieldAnalysisContext) Create(bool byRefArgument, bool reversed, bool valueOwner = false)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "Tests", "Owner", valueOwner ? app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType")!
                : app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var valueType = app.SystemTypes.SystemInt32Type;
        var field = new InjectedFieldAnalysisContext("Value", valueType, FieldAttributes.Public, owner, 8);
        owner.Fields.Add(field);
        var receiver = new LocalVariable("this", new Register(null, "this"), owner) { IsThis = true };
        var address = new LocalVariable("address", new Register(null, "address"), valueType);
        var target = new InjectedMethodAnalysisContext(valueType, "Consume", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | (byRefArgument ? MethodAttributes.Static : 0),
            byRefArgument ? [new ByRefTypeAnalysisContext(valueType)] : []);
        var call = new Instruction(1, OpCode.CallVoid, target, address);
        var method = new InjectedMethodAnalysisContext(owner, "Caller", app.SystemTypes.SystemVoidType, MethodAttributes.Public, [])
        {
            Locals = [receiver, address], ParameterLocals = [receiver],
            ControlFlowGraph = new ISILControlFlowGraph([
                new Instruction(0, OpCode.Add, address, reversed ? new Immediate(8) : receiver, reversed ? receiver : new Immediate(8)),
                call, new Instruction(2, OpCode.Return)]),
        };
        return (method, call, receiver, field);
    }
}
