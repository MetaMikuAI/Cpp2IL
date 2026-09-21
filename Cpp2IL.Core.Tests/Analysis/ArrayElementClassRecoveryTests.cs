using System.Collections.Generic;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ArrayElementClassRecoveryTests
{
    [TestCase("sameBlock", true)]
    [TestCase("dominatingBlock", true)]
    [TestCase("readBeforeStore", false)]
    [TestCase("conditionalStore", false)]
    [TestCase("multipleStores", false)]
    [TestCase("mutable", false)]
    [TestCase("instance", false)]
    [TestCase("otherOwner", false)]
    [TestCase("otherMethod", false)]
    [TestCase("addressTaken", false)]
    [TestCase("rawStorageAddress", false)]
    [TestCase("rawStorageStore", false)]
    [TestCase("unknownAllocation", false)]
    public void ProvesReadonlyArrayAllocationWithinItsStaticInitializer(string shape, bool expected)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var root = app.SystemTypes.SystemObjectType;
        var owner = new InjectedTypeAnalysisContext(root.DeclaringAssembly, "Tests", "ArrayOwner", root, TypeAttributes.Public);
        var declared = new SzArrayTypeAnalysisContext(root);
        var actual = new SzArrayTypeAnalysisContext(app.SystemTypes.SystemStringType);
        var attributes = FieldAttributes.Static | FieldAttributes.InitOnly;
        if (shape == "mutable") attributes &= ~FieldAttributes.InitOnly;
        if (shape == "instance") attributes &= ~FieldAttributes.Static;
        var field = new InjectedFieldAnalysisContext("Values", declared, attributes, shape == "otherOwner" ? root : owner, 0);
        var storage = new LocalVariable("storage", new Register(null, "storage"), new StaticFieldStorageTypeAnalysisContext(owner, owner.DeclaringAssembly));
        var allocated = new LocalVariable("allocated", new Register(null, "allocated"), declared);
        var array = new LocalVariable("array", new Register(null, "array"), declared);
        var klass = new LocalVariable("klass", new Register(null, "klass"));
        var element = new LocalVariable("element", new Register(null, "element"));
        var condition = new LocalVariable("condition", new Register(null, "condition"), app.SystemTypes.SystemBooleanType);
        var store = new Instruction(1, OpCode.Move, new FieldReference(field, storage, 0), allocated);
        var read = new Instruction(2, OpCode.Move, array, new FieldReference(field, storage, 0));
        var load = new Instruction(4, OpCode.Move, element, new MemoryOperand(klass, addend: 0x40));
        var instructions = new List<Instruction>
        {
            shape == "unknownAllocation" ? new(0, OpCode.Nop) : new(0, OpCode.NewArr, allocated, actual, new Immediate(1)),
            store, read, new(3, OpCode.Move, klass, new MemoryOperand(array)), load, new(5, OpCode.Return)
        };
        switch (shape)
        {
            case "dominatingBlock": instructions.Insert(2, new(6, OpCode.Jump, read)); break;
            case "readBeforeStore": instructions.Remove(read); instructions.Insert(1, read); break;
            case "conditionalStore": instructions.Insert(1, new(6, OpCode.ConditionalJump, read, condition)); break;
            case "multipleStores": instructions.Insert(2, new(6, OpCode.Move, new FieldReference(field, storage, 0), allocated)); break;
            case "addressTaken": instructions.Insert(2, new(6, OpCode.CallVoid, new Immediate(123), new AddressOf(new FieldReference(field, storage, 0)))); break;
            case "rawStorageAddress": instructions.Insert(2, new(6, OpCode.CallVoid, new Immediate(123), storage)); break;
            case "rawStorageStore": instructions.Insert(2, new(6, OpCode.Move, new MemoryOperand(storage), new Immediate(0))); break;
        }
        var method = new InjectedMethodAnalysisContext(owner, shape == "otherMethod" ? "Initialize" : ".cctor", app.SystemTypes.SystemVoidType,
            MethodAttributes.Static | MethodAttributes.Public, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph(instructions),
            Locals = [storage, allocated, array, klass, element, condition], ParameterLocals = []
        };
        ArrayElementClassRecovery.Run(method);
        Assert.That(load.Operands[1] is RuntimeClassTypeAnalysisContext, Is.EqualTo(expected));
        if (expected)
            Assert.That(((RuntimeClassTypeAnalysisContext)load.Operands[1]).RepresentedType, Is.SameAs(app.SystemTypes.SystemStringType),
                "The allocation, not the covariant declared object[] field type, proves the element class");
    }

    [TestCase("metadata", true)]
    [TestCase("copy", true)]
    [TestCase("static_type_only", false)]
    [TestCase("mixed_phi", false)]
    [TestCase("value_type", false)]
    public void IsInstAcceptsExactMetadataButNotAnInferredRuntimeClass(string kind, bool expected)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var target = app.SystemTypes.SystemStringType;
        var handle = new LocalVariable("handle", new Register(null, "handle"),
            new RuntimeClassTypeAnalysisContext(target, target.DeclaringAssembly));
        var result = new LocalVariable("result", new Register(null, "result"));
        var definition = kind switch
        {
            "copy" => new Instruction(0, OpCode.Move, handle, target),
            "mixed_phi" => new Instruction(0, OpCode.Phi, handle, target, app.SystemTypes.SystemObjectType),
            _ => new Instruction(0, OpCode.Nop)
        };
        IOperand klass = kind == "metadata" ? target : kind == "value_type" ? app.SystemTypes.SystemInt32Type : handle;
        var call = new Instruction(1, OpCode.Call, new StringLiteral("il2cpp_vm_object_is_inst"), result, new StringLiteral("value"), klass);
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Cast", app.SystemTypes.SystemObjectType,
            MethodAttributes.Static | MethodAttributes.Public, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([definition, call, new(2, OpCode.Return, result)]),
            Locals = [handle, result], ParameterLocals = []
        };
        KeyFunctionRecovery.Run(method);
        Assert.That(call.OpCode, Is.EqualTo(expected ? OpCode.TryCast : OpCode.Call));
        if (expected) Assert.That(call.Operands[1], Is.SameAs(target));
    }

    [TestCase("newarr", true)]
    [TestCase("helper", true)]
    [TestCase("parameter", false)]
    [TestCase("mixed", false)]
    [TestCase("wrong_offset", false)]
    public void RequiresExactArrayClassRatherThanCovariantStaticType(string kind, bool expected)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var actual = new SzArrayTypeAnalysisContext(app.SystemTypes.SystemStringType);
        var array = new LocalVariable("array", new Register(null, "array"), new SzArrayTypeAnalysisContext(app.SystemTypes.SystemObjectType));
        var klass = new LocalVariable("klass", new Register(null, "klass"));
        var element = new LocalVariable("element", new Register(null, "element"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var source = new LocalVariable("other", new Register(null, "other"));
        var allocation = kind switch
        {
            "helper" => new Instruction(0, OpCode.Call, new StringLiteral("SzArrayNew"), array, actual, new Immediate(1)),
            "parameter" => new Instruction(0, OpCode.Nop),
            "mixed" => new Instruction(0, OpCode.Phi, array, source, new Immediate(0)),
            _ => new Instruction(0, OpCode.NewArr, array, actual, new Immediate(1))
        };
        var load = new Instruction(2, OpCode.Move, element, new MemoryOperand(klass, addend: kind == "wrong_offset" ? 0x48 : 0x40));
        var call = new Instruction(3, OpCode.Call, new StringLiteral("il2cpp_vm_object_is_inst"), result, new StringLiteral("value"), element);
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Store", app.SystemTypes.SystemObjectType,
            MethodAttributes.Static | MethodAttributes.Public, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([allocation, new(1, OpCode.Move, klass, new MemoryOperand(array)), load, call, new(4, OpCode.Return, result)]),
            Locals = [array, klass, element, result, source], ParameterLocals = []
        };
        KeyFunctionRecovery.Run(method);
        Assert.That(load.Operands[1] is RuntimeClassTypeAnalysisContext, Is.EqualTo(expected));
        Assert.That(call.OpCode, Is.EqualTo(expected ? OpCode.TryCast : OpCode.Call));
        if (expected) Assert.That(call.Operands[1], Is.SameAs(app.SystemTypes.SystemStringType));
    }
}
