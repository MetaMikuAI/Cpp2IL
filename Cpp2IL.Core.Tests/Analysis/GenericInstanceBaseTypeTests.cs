using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class GenericInstanceBaseTypeTests
{
    private ApplicationAnalysisContext _app = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
    }

    private InjectedTypeAnalysisContext GenericType(string name)
    {
        var root = _app.SystemTypes.SystemObjectType;
        var type = new InjectedTypeAnalysisContext(root.DeclaringAssembly, "Tests", name, root, TypeAttributes.Public);
        type.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            GenericParameterAttributes.None, type));
        return type;
    }

    [Test]
    public void MetadataBackedInstancesRetainTheirBaseType()
    {
        var instances = _app.AllTypes.SelectMany(t => t.Fields).Select(f => f.FieldType)
            .OfType<GenericInstanceTypeAnalysisContext>().Where(t => t.GenericType.BaseType != null).ToList();
        Assert.That(instances, Is.Not.Empty);
        foreach (var instance in instances)
        {
            var constructed = instance.GenericType.MakeGenericInstanceType(instance.GenericArguments);
            var baseType = instance.BaseType;
            Assert.That(baseType, Is.Not.Null, instance.FullName);
            Assert.That(baseType!.FullName, Is.EqualTo(constructed.BaseType!.FullName));
            Assert.That(instance.BaseType, Is.SameAs(baseType));
        }
    }

    [TestCase(false)]
    [TestCase(true)]
    public void SubstitutesInheritedFieldType(bool is32Bit)
    {
        _app.Binary.is32Bit = is32Bit;
        var parent = GenericType("Parent`1");
        parent.Fields.Add(new InjectedFieldAnalysisContext("Value", parent.GenericParameters[0], FieldAttributes.Public, parent, 0));
        var child = GenericType("Child`1");
        child.BaseType = parent.MakeGenericInstanceType([child.GenericParameters[0]]);
        child.Fields.Add(new InjectedFieldAnalysisContext("OwnValue", _app.SystemTypes.SystemInt32Type, FieldAttributes.Public, child, 0));
        var instance = child.MakeGenericInstanceType([_app.SystemTypes.SystemStringType]);
        var baseType = (GenericInstanceTypeAnalysisContext)instance.BaseType!;
        Assert.That(baseType.GenericArguments.Single(), Is.SameAs(_app.SystemTypes.SystemStringType));
        Assert.That(instance.BaseType, Is.SameAs(baseType));
        Assert.That(GenericInstanceFieldLayout.FindFieldAtOffset(instance, 2 * _app.Binary.PointerSizeBytes), Is.Null,
            "The derived field must not occupy its generic base's storage");
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), instance);
        var result = new LocalVariable("result", new Register(null, "result"));
        var load = new Instruction(0, OpCode.Move, result, new MemoryOperand(receiver, addend: 2 * _app.Binary.PointerSizeBytes));
        var method = new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType, "Read", _app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([load, new(1, OpCode.Return)]),
            Locals = [receiver, result], ParameterLocals = []
        };
        LocalVariables.ResolveTypesAndFields(method);
        var field = ((FieldReference)load.Operands[1]).Field;
        Assert.That(field.DeclaringType, Is.SameAs(baseType));
        Assert.That(field.FieldType, Is.SameAs(_app.SystemTypes.SystemStringType));
        Assert.That(result.Type, Is.SameAs(_app.SystemTypes.SystemStringType));
    }

    [Test]
    public void SupportsSelfReferencingBaseArgumentsWithoutEagerRecursion()
    {
        var parent = GenericType("Parent`1");
        var child = GenericType("Child`1");
        child.BaseType = parent.MakeGenericInstanceType([child.MakeGenericInstanceType([child.GenericParameters[0]])]);
        var instance = child.MakeGenericInstanceType([_app.SystemTypes.SystemStringType]);
        var baseType = (GenericInstanceTypeAnalysisContext)instance.BaseType!;
        var argument = (GenericInstanceTypeAnalysisContext)baseType.GenericArguments.Single();
        Assert.That(argument.GenericType, Is.SameAs(child));
        Assert.That(argument.GenericArguments.Single(), Is.SameAs(_app.SystemTypes.SystemStringType));
        Assert.That(baseType.BaseType, Is.SameAs(_app.SystemTypes.SystemObjectType));
    }

    [Test]
    public void DoesNotInventAnInterfaceBaseClass()
    {
        var definition = new InjectedTypeAnalysisContext(_app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "Tests", "IContainer`1", null, TypeAttributes.Public | TypeAttributes.Interface);
        definition.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            GenericParameterAttributes.None, definition));
        Assert.That(definition.MakeGenericInstanceType([_app.SystemTypes.SystemStringType]).BaseType, Is.Null);
    }
}
