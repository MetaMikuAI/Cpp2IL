using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class OpenGenericRgctxTests
{
    private ApplicationAnalysisContext _app = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
    }

    private TypeAnalysisContext? Resolve(TypeAnalysisContext owner, int offset)
    {
        var table = new RgctxTableTypeAnalysisContext(owner, owner.DeclaringAssembly);
        var source = new LocalVariable("table", new Register(null, "table"), table);
        var result = new LocalVariable("entry", new Register(null, "entry"));
        var load = new Instruction(0, OpCode.Move, result, new MemoryOperand(source, addend: offset));
        var method = new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType, "Caller", _app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([load, new Instruction(1, OpCode.Return)]),
            Locals = [source, result], ParameterLocals = []
        };
        var changed = RgctxResolver.Run(method);
        Assert.That(RgctxResolver.Run(method), Is.False, "The resolved load must converge.");
        Assert.That(changed, Is.EqualTo(result.Type != null));
        return result.Type;
    }

    private static string Describe(TypeAnalysisContext? entry) => entry switch
    {
        RuntimeClassTypeAnalysisContext klass => "class:" + klass.RepresentedType.FullName,
        RuntimeMethodInfoAnalysisContext info => "method:" + info.RepresentedMethod.DeclaringType!.FullName
            + ":" + info.RepresentedMethod.Name + "(" + string.Join(",", info.RepresentedMethod.Parameters.Select(p => p.ParameterType.FullName))
            + "):" + info.RepresentedMethod.ReturnType.FullName,
        null => "unresolved",
        _ => entry.FullName
    };

    [TestCase("System.Collections.Generic.List`1")]
    [TestCase("System.Collections.Generic.Dictionary`2")]
    public void OpenTypeResolvesLikeInstantiationWithItsOwnFormalParameters(string name)
    {
        var definition = _app.AllTypes.Single(t => t.FullName == name);
        var formalInstance = definition.MakeGenericInstanceType(definition.GenericParameters);
        var concreteInstance = definition.MakeGenericInstanceType(definition.GenericParameters.Select(_ => _app.SystemTypes.SystemStringType));
        var entries = definition.Definition!.RgctXs;
        var affectedClasses = 0;
        var affectedMethods = 0;
        for (var index = 0; index < entries.Length; index++)
        {
            var offset = index * _app.Binary.PointerSizeBytes;
            var expected = Resolve(formalInstance, offset);
            var actual = Resolve(definition, offset);
            Assert.That(Describe(actual), Is.EqualTo(Describe(expected)), $"{name} RGCTX entry {index}");
            // Ensure the fixture actually exercises generic-dependent entries, rather than
            // passing solely because all entries are unresolved or independent of T.
            if (Describe(expected) == Describe(Resolve(concreteInstance, offset))) continue;
            if (expected is RuntimeClassTypeAnalysisContext) affectedClasses++;
            if (expected is RuntimeMethodInfoAnalysisContext) affectedMethods++;
        }
        Assert.That(affectedClasses, Is.GreaterThan(0));
        Assert.That(affectedMethods, Is.GreaterThan(0));
    }

    [TestCase(-8)]
    [TestCase(1)]
    [TestCase(1048576)]
    public void RejectsInvalidEntryOffsets(int offset)
    {
        var definition = _app.AllTypes.Single(t => t.FullName == "System.Collections.Generic.List`1");
        Assert.That(Resolve(definition, offset), Is.Null);
    }

    [Test]
    public void TypeWithoutMetadataIsNotGuessed()
    {
        var objectType = _app.SystemTypes.SystemObjectType;
        var owner = new InjectedTypeAnalysisContext(objectType.DeclaringAssembly, "Tests", "Unknown", objectType, TypeAttributes.Public);
        Assert.That(Resolve(owner, 0), Is.Null);
    }
}
