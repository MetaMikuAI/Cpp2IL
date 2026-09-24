using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class UnregisteredGenericCallTests
{
    private const uint LoadX1 = 0xF94002E1; // ldr x1, [x23]
    private const uint LoadX2 = 0xF94002E2; // ldr x2, [x23]
    private const uint Call = 0x94000010; // bl

    private sealed class KeyFunctions : NewArm64KeyFunctionAddresses
    {
        public override void Find(ApplicationAnalysisContext context) => Init(context);

        public void Publish() => InitializeResolvedAddresses();
    }

    private sealed class Arm64 : NewArmV8InstructionSet
    {
        public override BaseKeyFunctionAddresses CreateKeyFunctionAddressesInstance() => new KeyFunctions();
    }

    private ApplicationAnalysisContext _app = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
        _app.InstructionSet = new Arm64();
    }

    // A managed-code address that neither metadata nor the concrete generic table knows.
    private ulong UnregisteredAddress()
    {
        var address = _app.ManagedCodeStart + 1;
        Assume.That(address, Is.LessThan(_app.ManagedCodeEnd));
        Assume.That(_app.MethodsByAddress.ContainsKey(address), Is.False);
        Assume.That(_app.Binary.ConcreteGenericImplementationsByAddress.ContainsKey(address), Is.False);
        return address;
    }

    // Builder`1<Int32>::get_Task, an instance method whose declaring type is a generic instance
    private MethodAnalysisContext GenericGetter(bool genericOwner = true, string name = "get_Task")
    {
        var objectType = _app.SystemTypes.SystemObjectType;
        var owner = new InjectedTypeAnalysisContext(objectType.DeclaringAssembly, "Tests", genericOwner ? "Builder`1" : "Builder", objectType, TypeAttributes.Public);
        if (genericOwner)
            owner.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
                GenericParameterAttributes.None, owner));
        var getter = new InjectedMethodAnalysisContext(owner, name, objectType, MethodAttributes.Public, []);
        return genericOwner ? new ConcreteGenericMethodAnalysisContext(getter, [_app.SystemTypes.SystemInt32Type], []) : getter;
    }

    private static IOperand MethodInfo(MethodAnalysisContext method) =>
        new LocalVariable("info", new Register(null, "X1", 0), new RuntimeMethodInfoAnalysisContext(method, method.DeclaringType!.DeclaringAssembly));

    // Raw ARM64 call: result, X0-X7, V0-V7. The caller's code is `word; bl target` at 4 and 8.
    private (MethodAnalysisContext Caller, Instruction Call) Create(ulong target, Dictionary<int, IOperand> arguments, uint word = LoadX1)
    {
        var operands = new List<IOperand> { new Immediate(unchecked((long)target)), new LocalVariable("result", new Register(null, "X0", 1)) };
        for (var i = 0; i < 16; i++)
        {
            var name = i < 8 ? "X" + i : "V" + (i - 8);
            operands.Add(arguments.TryGetValue(i, out var argument) ? argument : new LocalVariable(name.ToLowerInvariant(), new Register(null, name, 0)));
        }

        var call = new Instruction(1, OpCode.Call, operands) { NativeAddress = 8 };
        var bytes = new byte[12];
        BinaryPrimitives.WriteUInt32LittleEndian(bytes.AsSpan(4), word);
        BinaryPrimitives.WriteUInt32LittleEndian(bytes.AsSpan(8), Call);
        var caller = new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType, "Caller", _app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([new(0, OpCode.Nop) { NativeAddress = 4 }, call, new(2, OpCode.Return) { NativeAddress = 12 }]),
            Locals = operands.OfType<LocalVariable>().ToList(), ParameterLocals = [],
            RawBytes = new BinarySlice(bytes),
        };
        return (caller, call);
    }

    [Test]
    public void BindsUnregisteredBodyToMethodInfoInHiddenSlot()
    {
        var address = UnregisteredAddress();
        var getter = GenericGetter();
        var receiver = new LocalVariable("builder", new Register(null, "X20", 0));
        var (caller, call) = Create(address, new() { [0] = receiver, [1] = MethodInfo(getter) });

        Assert.That(MetadataResolver.ResolveCallsViaMethodInfo(caller), Is.True);
        Assert.That(call.Operands[0], Is.SameAs(getter));
        Assert.That(call.Operands[2], Is.SameAs(receiver));
        // Shared bodies serve several instantiations, so the address stays unregistered.
        Assert.That(_app.MethodsByAddress.ContainsKey(address), Is.False);
    }

    [Test]
    public void RejectsNonGenericMethod()
    {
        var getter = GenericGetter(genericOwner: false);
        var (caller, call) = Create(UnregisteredAddress(), new() { [1] = MethodInfo(getter) });
        Assert.That(MetadataResolver.ResolveCallsViaMethodInfo(caller), Is.False);
        Assert.That(call.Operands[0], Is.InstanceOf<Immediate>());
    }

    [Test]
    public void RejectsAddressOutsideManagedCode()
    {
        var getter = GenericGetter();
        var (caller, call) = Create(_app.ManagedCodeEnd + 0x1000, new() { [1] = MethodInfo(getter) });
        Assert.That(MetadataResolver.ResolveCallsViaMethodInfo(caller), Is.False);
        Assert.That(call.Operands[0], Is.InstanceOf<Immediate>());
    }

    [Test]
    public void RejectsKeyFunction()
    {
        var address = UnregisteredAddress();
        var keys = (KeyFunctions)_app.GetOrCreateKeyFunctionAddresses();
        keys.il2cpp_vm_object_box = address;
        keys.Publish();
        var (caller, _) = Create(address, new() { [1] = MethodInfo(GenericGetter()) });
        Assert.That(MetadataResolver.ResolveCallsViaMethodInfo(caller), Is.False);
    }

    [Test]
    public void RejectsMethodInfoOutsideHiddenSlot()
    {
        // X1 is the hidden slot of an instance getter; a MethodInfo in X2 belongs to something else.
        var (caller, _) = Create(UnregisteredAddress(), new() { [2] = MethodInfo(GenericGetter()) }, LoadX2);
        Assert.That(MetadataResolver.ResolveCallsViaMethodInfo(caller), Is.False);
    }

    [Test]
    public void RejectsHiddenSlotHoldingAnotherMethodInfo()
    {
        var getter = GenericGetter();
        var (caller, _) = Create(UnregisteredAddress(), new() { [1] = MethodInfo(GenericGetter(name: "get_Other")), [5] = MethodInfo(getter) });
        Assert.That(MetadataResolver.ResolveCallsViaMethodInfo(caller), Is.False);
    }

    [TestCase(Call)] // a call in between clobbers X1, so the MethodInfo is left over from it
    [TestCase(0xF94002E2u)] // ldr x2: X1 is not set for this call at all
    [TestCase(0xD65F03C0u)] // ret: the call is only reached by a branch from elsewhere
    public void RejectsMethodInfoNotSetForThisCall(uint word)
    {
        var (caller, call) = Create(UnregisteredAddress(), new() { [1] = MethodInfo(GenericGetter()) }, word);
        Assert.That(MetadataResolver.ResolveCallsViaMethodInfo(caller), Is.False);
        Assert.That(call.Operands[0], Is.InstanceOf<Immediate>());
    }
}
