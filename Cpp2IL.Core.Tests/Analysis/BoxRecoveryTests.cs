using System;
using System.Collections.Generic;
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
        if (valueKind == "unknown")
            Assert.That(value.Type, expected ? Is.SameAs(type) : Is.Null);
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
        Check(new Immediate(unchecked((long)address)), expected, valueKind: "unknown");
    }

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
        Check(new Immediate(unchecked((long)address)), false, dynamicClass, "unknown");
    }

    [TestCase("copy", true)]
    [TestCase("runtimeClass", true)]
    [TestCase("mixedClass", false)]
    [TestCase("mixedAddress", false)]
    [TestCase("typedOnly", false)]
    [TestCase("cycle", false)]
    [TestCase("multipleDefinitions", false)]
    [TestCase("mismatch", false)]
    [TestCase("wrongHelper", false)]
    public void RecoversOnlyProvenMetadataAndAddressCopies(string shape, bool expected)
    {
        var address = _app.Binary.GetVirtualAddressOfPrimaryExecutableSection();
        _app.Binary.BaseStream.Position = _app.Binary.MapVirtualAddressToRaw(address);
        _app.Binary.BaseStream.Write(BitConverter.GetBytes(0x14000004u));
        _app.GetOrCreateKeyFunctionAddresses().il2cpp_vm_object_box = address + (shape == "wrongHelper" ? 32u : 16u);
        var type = _app.SystemTypes.SystemInt32Type;
        var value = new LocalVariable("value", new Register(null, "value"), shape == "mismatch" ? _app.SystemTypes.SystemInt64Type : null);
        var result = new LocalVariable("result", new Register(null, "result"));
        var klass = new LocalVariable("klass", new Register(null, "klass"));
        var classCopy = new LocalVariable("classCopy", new Register(null, "classCopy"));
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var pointerCopy = new LocalVariable("pointerCopy", new Register(null, "pointerCopy"));
        var classLoad = new Instruction(0, OpCode.Move, klass,
            shape == "runtimeClass" ? new RuntimeClassTypeAnalysisContext(type, type.DeclaringAssembly) : type);
        var classPhi = new Instruction(1, OpCode.Phi, classCopy, klass);
        var pointerLoad = new Instruction(2, OpCode.Move, pointer, new AddressOf(value));
        var pointerPhi = new Instruction(3, OpCode.Phi, pointerCopy, pointer);
        var call = new Instruction(4, OpCode.Call, new Immediate(unchecked((long)address)), result, classCopy, pointerCopy);
        var instructions = new List<Instruction> { classLoad, classPhi, pointerLoad, pointerPhi, call, new(5, OpCode.Return, result) };
        switch (shape)
        {
            case "mixedClass": classPhi.SetOperands(classCopy, klass, _app.SystemTypes.SystemInt64Type); break;
            case "mixedAddress": pointerPhi.SetOperands(pointerCopy, pointer, new Immediate(0)); break;
            case "typedOnly":
                klass.Type = new RuntimeClassTypeAnalysisContext(type, type.DeclaringAssembly);
                classLoad.OpCode = OpCode.Nop;
                classLoad.SetOperands();
                break;
            case "cycle": pointerLoad.SetOperand(1, pointerCopy); break;
            case "multipleDefinitions": instructions.Insert(1, new(6, OpCode.Move, klass, type)); break;
        }
        var method = new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType, "BoxCopies", _app.SystemTypes.SystemObjectType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph(instructions),
            Locals = [value, result, klass, classCopy, pointer, pointerCopy], ParameterLocals = []
        };
        KeyFunctionRecovery.Run(method);
        Assert.That(call.OpCode, Is.EqualTo(expected ? OpCode.Box : OpCode.Call));
        if (expected)
        {
            Assert.That(call.Operands, Is.EqualTo(new IOperand[] { result, type, new AddressOf(value) }));
            Assert.That(value.Type, Is.SameAs(type));
        }
        else if (shape != "mismatch")
            Assert.That(value.Type, Is.Null, "Rejected evidence must not type the stack value");
    }
}
