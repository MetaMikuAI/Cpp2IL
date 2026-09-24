using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ObjectIsInstRecoveryTests
{
    [TestCase("class", true)]
    [TestCase("baseClass", true)]
    [TestCase("none", false)]
    [TestCase("struct", false)]
    [TestCase("interface", false)]
    [TestCase("object", false)]
    [TestCase("valueType", false)]
    [TestCase("enum", false)]
    public void OnlyRecoversGenericTargetsProvenToBeReferences(string constraint, bool expected)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var owner = app.SystemTypes.SystemObjectType;
        var type = new GenericParameterTypeAnalysisContext("T", 0, LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            constraint == "class" ? GenericParameterAttributes.ReferenceTypeConstraint
                : constraint == "struct" ? GenericParameterAttributes.NotNullableValueTypeConstraint : GenericParameterAttributes.None, owner);
        var baseType = constraint switch
        {
            "baseClass" => app.SystemTypes.SystemExceptionType,
            "object" => owner,
            "valueType" => app.AllTypes.Single(t => t.FullName == "System.ValueType"),
            "enum" => app.AllTypes.Single(t => t.FullName == "System.Enum"),
            "interface" => app.AllTypes.First(t => t.IsInterface),
            _ => null
        };
        if (baseType != null) type.ConstraintTypes.Add(baseType);
        var result = new LocalVariable("result", new Register(null, "result"));
        var call = new Instruction(0, OpCode.Call, new StringLiteral("il2cpp_vm_object_is_inst"), result, new Immediate(0),
            new RuntimeClassTypeAnalysisContext(type, type.DeclaringAssembly));
        var method = new InjectedMethodAnalysisContext(owner, "Caller", owner, MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([call, new(1, OpCode.Return, result)]),
            Locals = [result], ParameterLocals = []
        };
        KeyFunctionRecovery.Run(method);
        Assert.That(call.OpCode, Is.EqualTo(expected ? OpCode.TryCast : OpCode.Call));
        if (expected) Assert.That(result.Type, Is.SameAs(type));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void RecoversReferenceResultThroughCopiesAndSingleInputPhi(bool nullObject)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var type = app.SystemTypes.SystemStringType;
        var klass = new RuntimeClassTypeAnalysisContext(type, type.DeclaringAssembly);
        var source = new LocalVariable("klass", new Register(null, "klass"), klass);
        var phi = new LocalVariable("phi", new Register(null, "phi"));
        var argument = new LocalVariable("arg", new Register(null, "arg"));
        var result = new LocalVariable("result", new Register(null, "result"));
        IOperand value = nullObject ? new Immediate(0) : new StringLiteral("hello");
        var call = new Instruction(3, OpCode.Call, new StringLiteral("il2cpp_vm_object_is_inst"), result, value, argument);
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", type,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([
                new(0, OpCode.Move, source, klass), new(1, OpCode.Phi, phi, source), new(2, OpCode.Move, argument, phi),
                call, new(4, OpCode.Return, result)]),
            Locals = [source, phi, argument, result], ParameterLocals = []
        };
        KeyFunctionRecovery.Run(method);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.TryCast));
        Assert.That(call.Operands, Is.EqualTo(new IOperand[] { result, type, value }));
        Assert.That(result.Type, Is.SameAs(type));
        Assert.That(call.Destination, Is.SameAs(result));
        Assert.That(call.SourcesAndConstants, Does.Contain(value));
        KeyFunctionRecovery.Run(method);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.TryCast));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void DoesNotGuessDynamicClassPointersOrMixedPhis(bool mixedPhi)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var type = app.SystemTypes.SystemStringType;
        var klass = new RuntimeClassTypeAnalysisContext(type, type.DeclaringAssembly);
        var argument = new LocalVariable("class", new Register(null, "class"), klass);
        var result = new LocalVariable("result", new Register(null, "result"));
        var call = new Instruction(1, OpCode.Call, new StringLiteral("il2cpp_vm_object_is_inst"), result, new StringLiteral("hello"), argument);
        var source = mixedPhi
            ? new Instruction(0, OpCode.Phi, argument, klass, new RuntimeClassTypeAnalysisContext(app.SystemTypes.SystemObjectType, type.DeclaringAssembly))
            : new Instruction(0, OpCode.Move, argument, new MemoryOperand(new LocalVariable("object", new Register(null, "object"))));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemObjectType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([source, call, new(2, OpCode.Return, result)]),
            Locals = [argument, result], ParameterLocals = []
        };
        KeyFunctionRecovery.Run(method);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
    }

    [TestCase("other_helper", false, false)]
    [TestCase("il2cpp_vm_object_is_inst", true, false)]
    [TestCase("il2cpp_vm_object_is_inst", false, true)]
    public void RejectsOtherHelpersAndValueTypeTargets(string name, bool valueType, bool genericTarget)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var type = valueType ? app.SystemTypes.SystemInt32Type : app.SystemTypes.SystemStringType;
        if (genericTarget)
            type = new GenericParameterTypeAnalysisContext("T", 0, LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_VAR,
                GenericParameterAttributes.None, app.SystemTypes.SystemObjectType);
        var result = new LocalVariable("result", new Register(null, "result"));
        var call = new Instruction(0, OpCode.Call, new StringLiteral(name), result, new StringLiteral("hello"),
            new RuntimeClassTypeAnalysisContext(type, type.DeclaringAssembly));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemObjectType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([call, new(1, OpCode.Return, result)]),
            Locals = [result], ParameterLocals = []
        };
        KeyFunctionRecovery.Run(method);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
    }

    [TestCase("valueType", "nullTest", OpCode.IsInstance)]
    [TestCase("openGeneric", "nullTest", OpCode.IsInstance)]
    [TestCase("valueType", "returned", OpCode.Call)]
    [TestCase("openGeneric", "comparedWithOther", OpCode.Call)]
    [TestCase("reference", "nullTest", OpCode.TryCast)]
    public void TestsAnyTypeWhenTheResultIsOnlyComparedWithNull(string target, string use, OpCode expected)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var owner = app.SystemTypes.SystemObjectType;
        TypeAnalysisContext type = target switch
        {
            "valueType" => app.SystemTypes.SystemInt32Type,
            "openGeneric" => new GenericParameterTypeAnalysisContext("T", 0, LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_MVAR,
                GenericParameterAttributes.None, owner),
            _ => app.SystemTypes.SystemStringType
        };
        var value = new LocalVariable("value", new Register(null, "value"), owner);
        var other = new LocalVariable("other", new Register(null, "other"), owner);
        var result = new LocalVariable("result", new Register(null, "result"));
        var test = new LocalVariable("test", new Register(null, "test"), app.SystemTypes.SystemBooleanType);
        var call = new Instruction(0, OpCode.Call, new StringLiteral("il2cpp_vm_object_is_inst"), result, value,
            new RuntimeClassTypeAnalysisContext(type, type.DeclaringAssembly));
        var consumer = use switch
        {
            "returned" => new Instruction(1, OpCode.Return, result),
            "comparedWithOther" => new Instruction(1, OpCode.CheckEqual, test, result, other),
            _ => new Instruction(1, OpCode.CheckEqual, test, new Immediate(0), result)
        };
        var instructions = new List<Instruction> { call, consumer };
        if (use != "returned") instructions.Add(new(2, OpCode.Return, test));
        var method = new InjectedMethodAnalysisContext(owner, "Test", owner, MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph(instructions),
            Locals = [value, other, result, test], ParameterLocals = []
        };
        KeyFunctionRecovery.Run(method);
        Assert.That(call.OpCode, Is.EqualTo(expected));
        if (expected == OpCode.Call) return;
        Assert.That(call.Operands, Is.EqualTo(new IOperand[] { result, type, value }));
        Assert.That(result.Type, Is.SameAs(expected == OpCode.IsInstance ? app.SystemTypes.SystemBooleanType : type));
    }
}
