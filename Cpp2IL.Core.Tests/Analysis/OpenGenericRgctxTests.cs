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

    [TestCase("split", true)]
    [TestCase("copy", true)]
    [TestCase("wrong_offset", false)]
    [TestCase("variable_offset", false)]
    [TestCase("mixed_phi", false)]
    [TestCase("overflow", false)]
    public void ResolvesSplitMethodInfoClassAddressOnlyWithProvenOffsets(string kind, bool expected)
    {
        var owner = _app.AllTypes.Single(t => t.FullName == "System.Collections.Generic.List`1");
        var caller = new InjectedMethodAnalysisContext(owner, "Caller", _app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        var info = new LocalVariable("info", new Register(null, "info"), new RuntimeMethodInfoAnalysisContext(caller, owner.DeclaringAssembly));
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var copied = new LocalVariable("copied", new Register(null, "copied"));
        var result = new LocalVariable("klass", new Register(null, "klass"));
        var unknown = new LocalVariable("offset", new Register(null, "offset"));
        var offset = kind == "wrong_offset" ? 24L : kind == "overflow" ? long.MaxValue : 16L;
        var address = kind == "mixed_phi"
            ? new Instruction(0, OpCode.Phi, pointer, info, unknown)
            : new Instruction(0, OpCode.Add, pointer, info, kind == "variable_offset" ? unknown : new Immediate(offset));
        var copy = new Instruction(1, OpCode.Move, copied, pointer);
        var load = new Instruction(2, OpCode.Move, result, new MemoryOperand(kind == "copy" ? copied : pointer, addend: 16));
        caller.ControlFlowGraph = new ISILControlFlowGraph([address, copy, load, new(3, OpCode.Return)]);
        Assert.That(RgctxResolver.Run(caller), Is.EqualTo(expected));
        if (expected)
            Assert.That(((RuntimeClassTypeAnalysisContext)result.Type!).RepresentedType, Is.SameAs(owner));
        else
            Assert.That(load.Operands[1], Is.TypeOf<MemoryOperand>());
        Assert.That(RgctxResolver.Run(caller), Is.False);
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
