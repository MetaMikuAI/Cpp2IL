using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class MetadataResolverTests
{
    private ApplicationAnalysisContext _appContext = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _appContext = TestGameLoader.LoadSimple2022Game();
    }

    [Test]
    public void Resolves_shared_generic_delegate_constructor_for_the_allocated_type()
    {
        var mscorlib = _appContext.GetAssemblyByName("mscorlib")!;
        var func = mscorlib.GetTypeByFullName("System.Func`2")!;
        var openConstructor = func.Methods.Single(method => method.Name == ".ctor");
        var addressCandidate = openConstructor.MakeConcreteGenericMethod(
            [_appContext.SystemTypes.SystemObjectType, _appContext.SystemTypes.SystemObjectType], []);
        var allocatedType = func.MakeGenericInstanceType(
            [_appContext.SystemTypes.SystemStringType, _appContext.SystemTypes.SystemInt32Type]);

        var resolved = MetadataResolver.ResolveConstructorForAllocatedType([addressCandidate], allocatedType);

        Assert.That(resolved, Is.InstanceOf<ConcreteGenericMethodAnalysisContext>());
        var concrete = (ConcreteGenericMethodAnalysisContext)resolved!;
        Assert.Multiple(() =>
        {
            Assert.That(concrete.BaseMethodContext, Is.SameAs(openConstructor));
            Assert.That(concrete.TypeGenericParameters[0], Is.SameAs(_appContext.SystemTypes.SystemStringType));
            Assert.That(concrete.TypeGenericParameters[1], Is.SameAs(_appContext.SystemTypes.SystemInt32Type));
        });
    }

    [Test]
    public void Metadata_generic_delegate_instances_preserve_the_delegate_base_type()
    {
        var delegateInstance = _appContext.AllTypes
            .SelectMany(type => type.Fields.Select(field => field.FieldType)
                .Concat(type.Methods.Select(method => method.ReturnType))
                .Concat(type.Methods.SelectMany(method => method.Parameters.Select(parameter => parameter.ParameterType))))
            .OfType<GenericInstanceTypeAnalysisContext>()
            .First(instance => instance.GenericType.IsDelegate);

        Assert.Multiple(() =>
        {
            Assert.That(delegateInstance.BaseType, Is.SameAs(delegateInstance.GenericType.BaseType));
            Assert.That(delegateInstance.IsDelegate, Is.True);
        });
    }

    [Test]
    public void Does_not_resolve_a_delegate_constructor_without_matching_address_evidence()
    {
        var mscorlib = _appContext.GetAssemblyByName("mscorlib")!;
        var func = mscorlib.GetTypeByFullName("System.Func`2")!;
        var action = mscorlib.GetTypeByFullName("System.Action`1")!;
        var actionConstructor = action.Methods.Single(method => method.Name == ".ctor");
        var addressCandidate = actionConstructor.MakeConcreteGenericMethod(
            [_appContext.SystemTypes.SystemObjectType], []);
        var allocatedType = func.MakeGenericInstanceType(
            [_appContext.SystemTypes.SystemStringType, _appContext.SystemTypes.SystemInt32Type]);

        var resolved = MetadataResolver.ResolveConstructorForAllocatedType([addressCandidate], allocatedType);

        Assert.That(resolved, Is.Null);
    }
}
