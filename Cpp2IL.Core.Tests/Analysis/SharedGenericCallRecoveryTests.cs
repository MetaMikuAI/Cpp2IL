using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class SharedGenericCallRecoveryTests
{
    private ApplicationAnalysisContext _app = null!;
    private InjectedTypeAnalysisContext _holder = null!;
    private MethodAnalysisContext _constructor = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
        _app.InstructionSet = new NewArmV8InstructionSet();
        var corlib = _app.SystemTypes.SystemObjectType.DeclaringAssembly;
        _holder = corlib.InjectType("Tests", "Holder`1", corlib.GetTypeByFullName("System.ValueType"), TypeAttributes.Public | TypeAttributes.Sealed);
        _holder.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            GenericParameterAttributes.None, _holder));
        _constructor = _holder.InjectMethodContext(".ctor", _app.SystemTypes.SystemVoidType, MethodAttributes.Public, _holder.GenericParameters[0]);
    }

    private TypeAnalysisContext Enum(string name, TypeAnalysisContext underlying)
    {
        var corlib = _app.SystemTypes.SystemObjectType.DeclaringAssembly;
        var type = corlib.InjectType("Tests", name, _app.SystemTypes.EnumType, TypeAttributes.Public | TypeAttributes.Sealed);
        type.EnumUnderlyingType = underlying;
        return type;
    }

    // The receiver is the address of one stack local, taken on two paths and merged by a phi.
    private (MethodAnalysisContext Caller, Instruction Call) Create(TypeAnalysisContext localType, TypeAnalysisContext? otherLocalType = null)
    {
        var shared = GenericSharingTests.SharedEnum(_app, _app.SystemTypes.SystemInt32Type);
        _app.MethodsByAddress[0x4321] = [new ConcreteGenericMethodAnalysisContext(_constructor, [shared], [])];
        var local = new LocalVariable("value", new Register(null, "stack"), _holder.MakeGenericInstanceType([localType]));
        var other = otherLocalType == null ? local : new LocalVariable("other", new Register(null, "stack2"), _holder.MakeGenericInstanceType([otherLocalType]));
        var address = new LocalVariable("address", new Register(null, "X0"));
        var firstAddress = new LocalVariable("address1", new Register(null, "X0"));
        var secondAddress = new LocalVariable("address2", new Register(null, "X0"));
        var argument = new LocalVariable("argument", new Register(null, "X1"));
        var call = new Instruction(3, OpCode.CallVoid, new Immediate(0x4321), address, argument);
        var caller = new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType, "Caller", _app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([
                new(0, OpCode.Move, argument, new Immediate(7)),
                new(1, OpCode.Move, firstAddress, new AddressOf(local)),
                new(1, OpCode.Move, secondAddress, new AddressOf(other)),
                new(2, OpCode.Phi, address, firstAddress, secondAddress),
                call, new(4, OpCode.Return)]),
            Locals = [local, other, address, firstAddress, secondAddress, argument], ParameterLocals = []
        };
        return (caller, call);
    }

    [TestCase(false)]
    [TestCase(true)]
    public void SpecializesASharedEnumBodyToTheTypeOfTheAddressedLocal(bool afterSsa)
    {
        var intEnum = Enum("IntBacked", _app.SystemTypes.SystemInt32Type);
        var (caller, call) = Create(intEnum);

        Assert.That(SharedGenericCallRecovery.Run(caller, afterSsa), Is.True);
        var resolved = (ConcreteGenericMethodAnalysisContext)call.Operands[0];
        Assert.That(resolved.BaseMethodContext, Is.SameAs(_constructor));
        Assert.That(resolved.TypeGenericParameters, Is.EqualTo(new[] { intEnum }));
        // In SSA, type resolution reruns and types the argument; out of it the pass does.
        Assert.That(((LocalVariable)call.Operands[2]).Type, afterSsa ? Is.SameAs(intEnum) : Is.Null);
        Assert.That(SharedGenericCallRecovery.Run(caller, afterSsa), Is.False);
    }

    [Test]
    public void LeavesTheCallWhenTheBodyCannotServeTheReceiver()
    {
        var (caller, call) = Create(Enum("LongBacked", _app.SystemTypes.SystemInt64Type));
        Assert.That(SharedGenericCallRecovery.Run(caller), Is.False);
        Assert.That(call.Operands[0], Is.InstanceOf<Immediate>());
    }

    [Test]
    public void LeavesTheCallWhenThePhiMergesDifferentTypes()
    {
        var intEnum = Enum("IntBacked", _app.SystemTypes.SystemInt32Type);
        var (caller, call) = Create(intEnum, Enum("OtherIntBacked", _app.SystemTypes.SystemInt32Type));
        Assert.That(SharedGenericCallRecovery.Run(caller), Is.False);
        Assert.That(call.Operands[0], Is.InstanceOf<Immediate>());
    }

    [Test]
    public void LeavesTheCallWhenAnInputOfThePhiIsUntyped()
    {
        var intEnum = Enum("IntBacked", _app.SystemTypes.SystemInt32Type);
        var (caller, call) = Create(intEnum);
        var untyped = new LocalVariable("unknown", new Register(null, "X0"));
        var phi = caller.ControlFlowGraph!.Instructions.Single(i => i.OpCode == OpCode.Phi);
        phi.SetOperand(2, untyped);
        Assert.That(SharedGenericCallRecovery.Run(caller), Is.False);
        Assert.That(call.Operands[0], Is.InstanceOf<Immediate>());
    }
}
