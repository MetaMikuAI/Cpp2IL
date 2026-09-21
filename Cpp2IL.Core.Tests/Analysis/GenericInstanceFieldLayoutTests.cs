using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class GenericInstanceFieldLayoutTests
{
    private ApplicationAnalysisContext _app = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
    }

    private GenericInstanceTypeAnalysisContext Create(TypeAnalysisContext argument, bool array)
    {
        var root = _app.SystemTypes.SystemObjectType;
        var definition = new InjectedTypeAnalysisContext(root.DeclaringAssembly, "Tests", "Container`1", root, TypeAttributes.Public);
        var parameter = new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            GenericParameterAttributes.None, definition);
        definition.GenericParameters.Add(parameter);
        definition.Fields.Add(new InjectedFieldAnalysisContext("data", array ? new SzArrayTypeAnalysisContext(parameter) : parameter,
            FieldAttributes.Public, definition, 0));
        definition.Fields.Add(new InjectedFieldAnalysisContext("count", _app.SystemTypes.SystemInt32Type,
            FieldAttributes.Public, definition, 0));
        return definition.MakeGenericInstanceType([argument]);
    }

    [TestCase(false, false)]
    [TestCase(false, true)]
    [TestCase(true, false)]
    [TestCase(true, true)]
    public void ResolvesArrayAndFollowingFieldWithStructArgument(bool is32Bit, bool write)
    {
        _app.Binary.is32Bit = is32Bit;
        var argument = _app.AllTypes.Single(t => t.FullName == "System.Decimal");
        var owner = Create(argument, array: true);
        var pointerSize = _app.Binary.PointerSizeBytes;
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), owner);
        var data = new LocalVariable("data", new Register(null, "data"));
        var count = new LocalVariable("count", new Register(null, "count"));
        var memory = new MemoryOperand(receiver, addend: 2 * pointerSize);
        var access = write ? new Instruction(0, OpCode.Move, memory, data) : new Instruction(0, OpCode.Move, data, memory);
        var countAccess = new Instruction(1, OpCode.Move, count, new MemoryOperand(receiver, addend: 3 * pointerSize));
        var method = new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType, "UseContainer", _app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([access, countAccess, new(2, OpCode.Return)]),
            Locals = [receiver, data, count], ParameterLocals = []
        };
        LocalVariables.ResolveTypesAndFields(method);
        var field = (FieldReference)access.Operands[write ? 0 : 1];
        Assert.That(field.Field, Is.TypeOf<ConcreteGenericFieldAnalysisContext>());
        Assert.That(field.Field.DeclaringType, Is.SameAs(owner));
        Assert.That(((SzArrayTypeAnalysisContext)field.Field.FieldType).ElementType, Is.SameAs(argument));
        Assert.That(((FieldReference)countAccess.Operands[1]).Field.Name, Is.EqualTo("count"));
        Assert.That(count.Type, Is.SameAs(_app.SystemTypes.SystemInt32Type));
        Assert.That(MetadataResolver.ResolveFieldOffsets(method), Is.False);
    }

    [TestCase(false)]
    [TestCase(true)]
    public void MeasuresInlinePrimitiveAfterSubstitution(bool is32Bit)
    {
        _app.Binary.is32Bit = is32Bit;
        var owner = Create(_app.SystemTypes.SystemInt32Type, array: false);
        var start = 2 * _app.Binary.PointerSizeBytes;
        Assert.That(GenericInstanceFieldLayout.FindFieldAtOffset(owner, start)?.Name, Is.EqualTo("data"));
        Assert.That(GenericInstanceFieldLayout.FindFieldAtOffset(owner, start + 4)?.Name, Is.EqualTo("count"));
        Assert.That(GenericInstanceFieldLayout.FindFieldAtOffset(owner, start + 1), Is.Null);
        Assert.That(GenericInstanceFieldLayout.FindFieldAtOffset(owner, start + 8), Is.Null);
    }

    [Test]
    public void DoesNotGuessUnknownInlineStructLayout()
    {
        var argument = _app.AllTypes.Single(t => t.FullName == "System.Decimal");
        var owner = Create(argument, array: false);
        var start = 2 * _app.Binary.PointerSizeBytes;
        Assert.That(GenericInstanceFieldLayout.FindFieldAtOffset(owner, start), Is.Null);
        Assert.That(GenericInstanceFieldLayout.FindFieldAtOffset(owner, start + _app.Binary.PointerSizeBytes), Is.Null);
    }
}
