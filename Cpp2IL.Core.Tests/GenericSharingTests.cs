using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests;

public class GenericSharingTests
{
    private ApplicationAnalysisContext _app = null!;
    private AssemblyAnalysisContext _corlib = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
        _corlib = _app.SystemTypes.SystemObjectType.DeclaringAssembly;
    }

    internal static TypeAnalysisContext SharedEnum(ApplicationAnalysisContext app, TypeAnalysisContext underlying)
    {
        var corlib = app.SystemTypes.SystemObjectType.DeclaringAssembly;
        return corlib.GetTypeByFullName($"System.{underlying.Name}Enum") ?? Enum(corlib, "System", underlying.Name + "Enum", underlying, TypeAttributes.NotPublic);
    }

    private static TypeAnalysisContext Enum(AssemblyAnalysisContext assembly, string ns, string name, TypeAnalysisContext underlying, TypeAttributes visibility)
    {
        var type = assembly.InjectType(ns, name, assembly.AppContext.SystemTypes.EnumType, visibility | TypeAttributes.Sealed);
        type.EnumUnderlyingType = underlying;
        return type;
    }

    private TypeAnalysisContext Type(string fullName) => _app.AllTypes.Single(t => t.FullName == fullName);

    [Test]
    public void ObjectIsTheSharedFormOfReferenceTypesOnly()
    {
        var types = _app.SystemTypes;
        var parameter = new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_MVAR, GenericParameterAttributes.None, types.SystemObjectType);

        Assert.That(GenericSharing.IsSharedFormOf(types.SystemObjectType, types.SystemStringType), Is.True);
        Assert.That(GenericSharing.IsSharedFormOf(types.SystemObjectType, parameter), Is.True);
        Assert.That(GenericSharing.IsSharedFormOf(types.SystemObjectType, types.SystemInt32Type), Is.False);
        Assert.That(GenericSharing.IsSharedFormOf(types.SystemStringType, types.SystemObjectType), Is.False);
        Assert.That(GenericSharing.IsSharedRepresentative(types.SystemObjectType), Is.True);
        Assert.That(GenericSharing.IsSharedRepresentative(types.SystemStringType), Is.False);
    }

    [Test]
    public void AnEnumSharesTheCorlibEnumOfItsExactUnderlyingType()
    {
        var types = _app.SystemTypes;
        var shared = SharedEnum(_app, types.SystemInt32Type);
        var intEnum = Enum(_corlib, "Tests", "IntBacked", types.SystemInt32Type, TypeAttributes.Public);
        var longEnum = Enum(_corlib, "Tests", "LongBacked", types.SystemInt64Type, TypeAttributes.Public);
        var uintEnum = Enum(_corlib, "Tests", "UIntBacked", types.SystemUInt32Type, TypeAttributes.Public);

        Assert.That(GenericSharing.IsSharedRepresentative(shared), Is.True);
        Assert.That(GenericSharing.IsSharedFormOf(shared, intEnum), Is.True);
        Assert.That(GenericSharing.IsSharedFormOf(shared, longEnum), Is.False);
        Assert.That(GenericSharing.IsSharedFormOf(shared, uintEnum), Is.False);
        Assert.That(GenericSharing.IsSharedFormOf(shared, types.SystemInt32Type), Is.False, "an enum body never serves the underlying primitive");
        Assert.That(GenericSharing.IsSharedFormOf(intEnum, shared), Is.False);
        Assert.That(GenericSharing.IsSharedFormOf(SharedEnum(_app, types.SystemInt64Type), longEnum), Is.True);
    }

    [Test]
    public void OnlyTheInternalCorlibEnumIsARepresentative()
    {
        var types = _app.SystemTypes;
        var lookalike = Enum(_corlib, "System", "BooleanEnum", types.SystemBooleanType, TypeAttributes.Public);
        var misnamed = Enum(_corlib, "System", "CharEnum", types.SystemInt32Type, TypeAttributes.NotPublic);
        var intEnum = Enum(_corlib, "Tests", "IntBacked", types.SystemInt32Type, TypeAttributes.Public);

        Assert.That(GenericSharing.IsSharedRepresentative(lookalike), Is.False);
        Assert.That(GenericSharing.IsSharedRepresentative(misnamed), Is.False);
        Assert.That(GenericSharing.IsSharedRepresentative(intEnum), Is.False);
        Assert.That(GenericSharing.IsSharedFormOf(lookalike, Enum(_corlib, "Tests", "BoolBacked", types.SystemBooleanType, TypeAttributes.Public)), Is.False);
    }

    [Test]
    public void AValueTypeInstanceSharesItsArgumentsPositionally()
    {
        var types = _app.SystemTypes;
        var pair = Type("System.Collections.Generic.KeyValuePair`2");
        var shared = SharedEnum(_app, types.SystemInt32Type);
        var intEnum = Enum(_corlib, "Tests", "IntBacked", types.SystemInt32Type, TypeAttributes.Public);

        var sharedPair = pair.MakeGenericInstanceType([shared, types.SystemObjectType]);
        Assert.That(GenericSharing.IsSharedRepresentative(sharedPair), Is.True);
        Assert.That(GenericSharing.IsSharedFormOf(sharedPair, pair.MakeGenericInstanceType([intEnum, types.SystemStringType])), Is.True);
        Assert.That(GenericSharing.IsSharedFormOf(sharedPair, pair.MakeGenericInstanceType([intEnum, types.SystemInt32Type])), Is.False);
        Assert.That(GenericSharing.IsSharedFormOf(sharedPair, pair.MakeGenericInstanceType([types.SystemStringType, types.SystemStringType])), Is.False);
        Assert.That(GenericSharing.IsSharedFormOf(types.SystemObjectType, pair.MakeGenericInstanceType([intEnum, types.SystemStringType])), Is.False);
        Assert.That(GenericSharing.IsSharedRepresentative(pair.MakeGenericInstanceType([types.SystemInt32Type, types.SystemInt32Type])), Is.False);
        Assert.That(GenericSharing.IsSharedRepresentative(pair.MakeGenericInstanceType([types.SystemInt32Type, types.SystemObjectType])), Is.True);
    }

    [Test]
    public void AGenericParameterOfTheCallerIsRuledOutOnlyByItsConstraints()
    {
        var types = _app.SystemTypes;
        var shared = SharedEnum(_app, types.SystemInt32Type);
        GenericParameterTypeAnalysisContext Parameter(GenericParameterAttributes attributes)
            => new("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR, attributes, types.SystemObjectType);

        Assert.That(GenericSharing.IsSharedFormOf(types.SystemInt64Type, Parameter(GenericParameterAttributes.None)), Is.True);
        Assert.That(GenericSharing.IsSharedFormOf(shared, Parameter(GenericParameterAttributes.None)), Is.True);
        Assert.That(GenericSharing.IsSharedFormOf(shared, Parameter(GenericParameterAttributes.ReferenceTypeConstraint)), Is.False);
        Assert.That(GenericSharing.IsSharedFormOf(types.SystemObjectType, Parameter(GenericParameterAttributes.NotNullableValueTypeConstraint)), Is.False);
    }

    [Test]
    public void OnlyAnEnumArgumentPinsTheBodyRegisteredAtAnAddress()
    {
        var types = _app.SystemTypes;
        var pair = Type("System.Collections.Generic.KeyValuePair`2");
        var shared = SharedEnum(_app, types.SystemInt32Type);
        var intEnum = Enum(_corlib, "Tests", "IntBacked", types.SystemInt32Type, TypeAttributes.Public);
        var longEnum = Enum(_corlib, "Tests", "LongBacked", types.SystemInt64Type, TypeAttributes.Public);

        Assert.That(GenericSharing.MayServe([shared], [intEnum]), Is.True);
        Assert.That(GenericSharing.MayServe([shared], [longEnum]), Is.False);
        Assert.That(GenericSharing.MayServe([shared], [types.SystemStringType]), Is.False);
        // Full generic sharing and folded bodies can put any other instantiation at the same address.
        Assert.That(GenericSharing.MayServe([types.SystemObjectType], [types.SystemInt32Type]), Is.True);
        Assert.That(GenericSharing.MayServe([types.SystemInt32Type], [types.SystemStringType]), Is.True);
        Assert.That(GenericSharing.MayServe([pair.MakeGenericInstanceType([shared, types.SystemObjectType])],
            [pair.MakeGenericInstanceType([longEnum, types.SystemStringType])]), Is.False);
        Assert.That(GenericSharing.MayServe([pair.MakeGenericInstanceType([shared, types.SystemObjectType])],
            [pair.MakeGenericInstanceType([intEnum, types.SystemInt32Type])]), Is.True);
        Assert.That(GenericSharing.MayServe([shared], [intEnum, intEnum]), Is.False);
    }
}
