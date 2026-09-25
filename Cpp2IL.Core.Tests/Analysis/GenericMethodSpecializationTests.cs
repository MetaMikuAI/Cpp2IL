using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class GenericMethodSpecializationTests
{
    private ApplicationAnalysisContext _app = null!;
    private readonly Dictionary<string, MethodAnalysisContext> _definitions = new();

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
        _app.InstructionSet = new NewArmV8InstructionSet();
        _definitions.Clear();
    }

    // Synthetic methods avoid depending on which LINQ overloads survive test-game stripping.
    // The declaring type is deliberately neither generic nor System.Linq.Enumerable.
    private MethodAnalysisContext Definition(string name)
    {
        if (_definitions.TryGetValue(name, out var existing)) return existing;
        var objectType = _app.SystemTypes.SystemObjectType;
        var owner = new InjectedTypeAnalysisContext(objectType.DeclaringAssembly, "Tests", "Queries", objectType, TypeAttributes.Public);
        var method = new InjectedMethodAnalysisContext(owner, name, objectType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        var count = name == "Map" ? 2 : 1;
        for (var i = 0; i < count; i++)
            method.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T" + i, i, Il2CppTypeEnum.IL2CPP_TYPE_MVAR,
                GenericParameterAttributes.None, method));
        var sequence = new InjectedTypeAnalysisContext(objectType.DeclaringAssembly, "Tests", "Sequence`1", objectType, TypeAttributes.Public);
        sequence.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            GenericParameterAttributes.None, sequence));
        var predicate = new InjectedTypeAnalysisContext(objectType.DeclaringAssembly, "Tests", "Predicate`2", objectType, TypeAttributes.Public);
        for (var i = 0; i < 2; i++)
            predicate.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T" + i, i, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
                GenericParameterAttributes.None, predicate));
        var t = method.GenericParameters[0];
        method.ReturnType = t;
        method.Parameters.Add(new InjectedParameterAnalysisContext("source", sequence.MakeGenericInstanceType([t]), ParameterAttributes.None, 0, method));
        method.Parameters.Add(new InjectedParameterAnalysisContext("predicate", predicate.MakeGenericInstanceType([t, _app.SystemTypes.SystemBooleanType]),
            ParameterAttributes.None, 1, method));
        return _definitions[name] = method;
    }

    private (MethodAnalysisContext Caller, Instruction Call, ConcreteGenericMethodAnalysisContext Target) Create(
        string name = "Find", string before = "Object", string after = "String", string? metadataName = null)
    {
        var definition = Definition(name);
        TypeAnalysisContext Type(string simple) => _app.AllTypes.Single(t => t.FullName == "System." + simple);
        var beforeArgs = Enumerable.Repeat(Type("Object"), definition.GenericParameters.Count).ToArray();
        var afterArgs = beforeArgs.ToArray();
        beforeArgs[0] = Type(before);
        afterArgs[0] = Type(after);
        var shared = new ConcreteGenericMethodAnalysisContext(definition, [], beforeArgs);
        var target = new ConcreteGenericMethodAnalysisContext(metadataName == null ? definition : Definition(metadataName), [], afterArgs);
        var result = new LocalVariable("result", new Register(null, "X0", 1));
        var source = new LocalVariable("source", new Register(null, "X0", 0), target.Parameters[0].ParameterType);
        var predicate = new LocalVariable("predicate", new Register(null, "X1", 0));
        var info = new LocalVariable("info", new Register(null, "X2", 0), new RuntimeMethodInfoAnalysisContext(target, definition.DeclaringType!.DeclaringAssembly));
        var call = new Instruction(0, OpCode.Call, shared, result, source, predicate, info);
        var caller = new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType, "Caller", _app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([call, new Instruction(1, OpCode.Return)]),
            Locals = [result, source, predicate, info], ParameterLocals = []
        };
        return (caller, call, target);
    }

    [Test]
    public void EarlyTrimmingPreservesMetadataForSharedGenericSpecialization()
    {
        var (caller, call, target) = Create();
        CallArgumentTrimmer.Run(caller, preserveGenericMetadata: true);
        Assert.That(call.Operands.Count, Is.EqualTo(5));
        Assert.That(MetadataResolver.ResolveCallsViaMethodInfo(caller), Is.True);
        Assert.That(call.Operands[0], Is.SameAs(target));
        CallArgumentTrimmer.Run(caller);
        Assert.That(call.Operands.Count, Is.EqualTo(4));
    }

    [TestCase("Find")]
    [TestCase("OtherFind")]
    [TestCase("Map")]
    public void RefinesMethodArgumentsOnNonGenericDeclaringType(string name)
    {
        var (caller, call, target) = Create(name);
        Assert.That(MetadataResolver.ResolveCallsViaMethodInfo(caller), Is.True);
        Assert.That(call.Operands[0], Is.SameAs(target));
        Assert.That(MetadataResolver.ResolveCallsViaMethodInfo(caller), Is.False);
    }

    [TestCase("Object", "Object")]
    [TestCase("String", "Object")]
    [TestCase("String", "Exception")]
    [TestCase("Object", "Int32")]
    public void DoesNotChangeEqualConcreteOrValueTypeArguments(string before, string after)
    {
        var (caller, call, _) = Create(before: before, after: after);
        var original = call.Operands[0];
        Assert.That(MetadataResolver.ResolveCallsViaMethodInfo(caller), Is.False);
        Assert.That(call.Operands[0], Is.SameAs(original));
    }

    // IL2CPP shares enum instantiations through the internal corlib enum of the same underlying type.
    [TestCase("Int32Enum", "TestIntEnum", true)]
    [TestCase("Int32Enum", "TestLongEnum", false)]
    [TestCase("Int32Enum", "Int32", false)]
    [TestCase("Object", "TestIntEnum", false)]
    public void RefinesSharedEnumBodiesOnlyToEnumsOfTheSameUnderlyingType(string before, string after, bool refines)
    {
        var types = _app.SystemTypes;
        var corlib = types.SystemObjectType.DeclaringAssembly;
        GenericSharingTests.SharedEnum(_app, types.SystemInt32Type);
        foreach (var (name, underlying) in new[] { ("TestIntEnum", types.SystemInt32Type), ("TestLongEnum", types.SystemInt64Type) })
            corlib.InjectType("System", name, types.EnumType, TypeAttributes.Public | TypeAttributes.Sealed).EnumUnderlyingType = underlying;

        var (caller, call, target) = Create(before: before, after: after);
        var original = call.Operands[0];
        Assert.That(MetadataResolver.ResolveCallsViaMethodInfo(caller), Is.EqualTo(refines));
        Assert.That(call.Operands[0], Is.SameAs(refines ? target : original));
    }

    [Test]
    public void RejectsMetadataForAnotherMethod()
    {
        var (caller, call, _) = Create(metadataName: "OtherFind");
        var original = call.Operands[0];
        Assert.That(MetadataResolver.ResolveCallsViaMethodInfo(caller), Is.False);
        Assert.That(call.Operands[0], Is.SameAs(original));
    }

    [Test]
    public void RequiresMethodInfoRatherThanGuessingFromArgumentTypes()
    {
        var (caller, call, _) = Create();
        call.RemoveOperandAt(call.Operands.Count - 1);
        Assert.That(MetadataResolver.ResolveCallsViaMethodInfo(caller), Is.False);
    }

    [Test]
    public void SpecializesBeforeReturnAndPredicateTypesArePropagated()
    {
        var (caller, call, target) = Create();
        LocalVariables.ResolveTypesAndFields(caller);
        Assert.That(call.Operands[0], Is.SameAs(target));
        Assert.That(((LocalVariable)call.Operands[1]).Type, Is.SameAs(_app.SystemTypes.SystemStringType));
        Assert.That(((LocalVariable)call.Operands[3]).Type!.FullName, Is.EqualTo("Tests.Predicate`2<System.String, System.Boolean>"));
    }
}
