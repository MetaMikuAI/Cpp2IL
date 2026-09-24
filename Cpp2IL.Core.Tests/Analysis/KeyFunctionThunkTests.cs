using System;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class KeyFunctionThunkTests
{
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
    private ulong _code;
    private KeyFunctions _keys = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
        _app.InstructionSet = new Arm64();
        _code = _app.Binary.GetVirtualAddressOfPrimaryExecutableSection();
        _keys = (KeyFunctions)_app.GetOrCreateKeyFunctionAddresses();
        // The boxing helper sits at +16; entries before it are candidate thunks.
        _keys.il2cpp_vm_object_box = _code + 16;
        _keys.Publish();
    }

    private void Write(ulong address, uint word)
    {
        _app.Binary.BaseStream.Position = _app.Binary.MapVirtualAddressToRaw(address);
        _app.Binary.BaseStream.Write(BitConverter.GetBytes(word));
    }

    [TestCase(0x14000004u, true)] // B to the key function
    [TestCase(0x94000004u, false)] // BL returns to the thunk, which then does something else
    [TestCase(0x54000080u, false)] // conditional B
    [TestCase(0xD65F03C0u, false)] // RET
    [TestCase(0x14000008u, false)] // B to an address that is not a key function
    public void ResolvesOnlySingleBranchThunks(uint word, bool expected)
    {
        Write(_code, word);
        Assert.That(_keys.IsKeyFunctionAddress(_code), Is.EqualTo(expected));
        Assert.That(_keys.ResolveKeyFunctionAddress(_code), Is.EqualTo(expected ? _code + 16 : 0));
    }

    [Test]
    public void KeyFunctionResolvesToItself()
    {
        Assert.That(_keys.ResolveKeyFunctionAddress(_code + 16), Is.EqualTo(_code + 16));
        Assert.That(_keys.IsKeyFunctionAddress(0), Is.False);
    }

    [Test]
    public void FollowsChainedThunks()
    {
        Write(_code, 0x14000002); // b +8
        Write(_code + 8, 0x14000002); // b +8
        Assert.That(_keys.ResolveKeyFunctionAddress(_code), Is.EqualTo(_code + 16));
    }

    [TestCase(true)]
    [TestCase(false)] // a pointer that is not the address of a local cannot be boxed by value
    public void CallThroughThunkIsHandledAsTheKeyFunction(bool localAddress)
    {
        Write(_code, 0x14000004);
        var type = _app.SystemTypes.SystemInt32Type;
        var value = new LocalVariable("value", new Register(null, "value"), type);
        var result = new LocalVariable("result", new Register(null, "result"));
        var call = new Instruction(0, OpCode.Call, new Immediate(unchecked((long)_code)), result, type, localAddress ? new AddressOf(value) : value);
        var method = new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType, "Box", _app.SystemTypes.SystemObjectType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([call, new(1, OpCode.Return, result)]),
            Locals = [value, result], ParameterLocals = []
        };

        MetadataResolver.ResolveAll(method);
        Assert.That(call.Operands[0], Is.EqualTo(new StringLiteral(nameof(BaseKeyFunctionAddresses.il2cpp_vm_object_box))));

        KeyFunctionRecovery.Run(method);
        Assert.That(call.OpCode, Is.EqualTo(localAddress ? OpCode.Box : OpCode.Call));
    }
}
