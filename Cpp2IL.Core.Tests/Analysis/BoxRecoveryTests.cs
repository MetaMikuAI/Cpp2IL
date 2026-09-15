using System;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class BoxRecoveryTests
{
    private sealed class KeyFunctions : NewArm64KeyFunctionAddresses
    {
        public override void Find(ApplicationAnalysisContext context) { }
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

    private void Check(IOperand target, bool expected, bool dynamicClass = false, string valueKind = "typed")
    {
        var type = _app.SystemTypes.SystemInt32Type;
        var value = new LocalVariable("value", new Register(null, "value"),
            valueKind == "unknown" ? null : valueKind == "mismatched" ? _app.SystemTypes.SystemInt64Type : type);
        var result = new LocalVariable("result", new Register(null, "result"));
        IOperand pointer = valueKind == "raw" ? value : new AddressOf(value);
        IOperand klass = dynamicClass ? new LocalVariable("class", new Register(null, "class")) : type;
        var call = new Instruction(0, OpCode.Call, target, result, klass, pointer);
        var method = new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType, "Box", _app.SystemTypes.SystemObjectType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([call, new(1, OpCode.Return, result)]),
            Locals = [value, result], ParameterLocals = []
        };
        KeyFunctionRecovery.Run(method);
        Assert.That(call.OpCode, Is.EqualTo(expected ? OpCode.Box : OpCode.Call));
        Assert.That(call.Operands, Is.EqualTo(expected
            ? new IOperand[] { result, type, pointer }
            : new IOperand[] { target, result, klass, pointer }));
        KeyFunctionRecovery.Run(method);
        Assert.That(call.OpCode, Is.EqualTo(expected ? OpCode.Box : OpCode.Call));
    }

    [TestCase("il2cpp_value_box", true)]
    [TestCase("il2cpp_vm_object_box", true)]
    [TestCase("other_helper", false)]
    public void PreservesNamedHelperRecovery(string name, bool expected) => Check(new StringLiteral(name), expected);

    [TestCase(0x14000004u, true)] // B to known implementation
    [TestCase(0x94000004u, false)] // BL must not be treated as an argument-preserving thunk
    [TestCase(0x54000080u, false)] // conditional B
    [TestCase(0xD65F03C0u, false)] // RET
    [TestCase(0xAA0103E0u, false)] // MOV changes an argument before any later branch
    [TestCase(0x14000008u, false)] // B to another implementation
    public void OnlyRecoversDirectBoxingThunks(uint word, bool expected)
    {
        var address = _app.Binary.GetVirtualAddressOfPrimaryExecutableSection();
        _app.Binary.BaseStream.Position = _app.Binary.MapVirtualAddressToRaw(address);
        _app.Binary.BaseStream.Write(BitConverter.GetBytes(word));
        _app.GetOrCreateKeyFunctionAddresses().il2cpp_vm_object_box = address + 16;
        Check(new Immediate(unchecked((long)address)), expected);
    }

    [TestCase("unknown")]
    [TestCase("mismatched")]
    [TestCase("raw")]
    public void DoesNotBoxUnsupportedPointees(string valueKind)
    {
        var address = _app.Binary.GetVirtualAddressOfPrimaryExecutableSection();
        _app.Binary.BaseStream.Position = _app.Binary.MapVirtualAddressToRaw(address);
        _app.Binary.BaseStream.Write(BitConverter.GetBytes(0x14000004u));
        _app.GetOrCreateKeyFunctionAddresses().il2cpp_vm_object_box = address + 16;
        Check(new Immediate(unchecked((long)address)), false, valueKind: valueKind);
    }

    [TestCase(false)]
    [TestCase(true)]
    public void RequiresKnownImplementationAndClass(bool dynamicClass)
    {
        var address = _app.Binary.GetVirtualAddressOfPrimaryExecutableSection();
        _app.Binary.BaseStream.Position = _app.Binary.MapVirtualAddressToRaw(address);
        _app.Binary.BaseStream.Write(BitConverter.GetBytes(0x14000004u));
        if (dynamicClass)
            _app.GetOrCreateKeyFunctionAddresses().il2cpp_vm_object_box = address + 16;
        Check(new Immediate(unchecked((long)address)), false, dynamicClass);
    }
}
