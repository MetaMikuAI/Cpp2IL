using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class GenericValueTypeMemberTests
{
    private ApplicationAnalysisContext _app = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
    }

    private TypeAnalysisContext Type(string name) => _app.AllTypes.Single(t => t.FullName == name);

    private GenericInstanceTypeAnalysisContext Pair(TypeAnalysisContext key, TypeAnalysisContext value)
        => Type("System.Collections.Generic.KeyValuePair`2").MakeGenericInstanceType([key, value]);

    private GenericInstanceTypeAnalysisContext Nullable(TypeAnalysisContext value)
        => Type("System.Nullable`1").MakeGenericInstanceType([value]);

    private TypeAnalysisContext Int16 => Type("System.Int16");
    private TypeAnalysisContext Int64 => Type("System.Int64");

    [Test]
    public void LaysOutGenericValueTypesFromTheirSubstitutedFields()
    {
        var pair = Pair(Int64, _app.SystemTypes.SystemStringType);
        Assert.That(GenericInstanceFieldLayout.ValueTypeSizeAndAlignment(pair), Is.EqualTo((16L, 8L)));
        Assert.That(GenericInstanceFieldLayout.ValueTypeSizeAndAlignment(Nullable(_app.SystemTypes.SystemInt32Type)), Is.EqualTo((8L, 4L)));

        // Nullable<KeyValuePair<int, int>> (value, then has_value): the 4-aligned pair is followed by
        // the flag at 8, and the whole rounds up to its 4-byte alignment.
        var nested = Nullable(Pair(_app.SystemTypes.SystemInt32Type, _app.SystemTypes.SystemInt32Type));
        Assert.That(GenericInstanceFieldLayout.ValueTypeSizeAndAlignment(nested), Is.EqualTo((12L, 4L)));
        var layout = GenericInstanceFieldLayout.ComputeLayout(nested)!.Value;
        Assert.That(layout.Complete, Is.True);
        Assert.That(layout.Slots.Select(s => (s.Field.Name, s.Offset, s.Size)).ToArray(),
            Is.EqualTo(new[] { ("value", 0L, 8L), ("has_value", 8L, 1L) }));
        Assert.That(layout.Slots.All(s => s.Field is ConcreteGenericFieldAnalysisContext && s.Field.DeclaringType == nested));
    }

    // Offsets are relative to the retyped field. Nullable<KeyValuePair<long, string>> holds the pair
    // (key at 0, value at 8) and then has_value at 0x10, padded to 0x18.
    [TestCase("nullablePair", 0x8, 8, true, new[] { "value" }, "value")]
    [TestCase("nullablePair", 0x8, 8, false, new[] { "value" }, "value")]
    [TestCase("nullablePair", 0x0, 8, true, new[] { "value" }, "key")]
    [TestCase("nullablePair", 0x0, 8, false, new[] { "value" }, "key")]
    [TestCase("nullablePair", 0x10, 8, true, new string[0], "has_value")]
    [TestCase("paddedPair", 0x8, 8, true, new string[0], "value")]
    [TestCase("paddedPair", 0x8, 2, false, new string[0], "value")]
    [TestCase("nullableIntPair", 0x4, 8, true, null, null)]
    [TestCase("shortPair", 0x2, 4, true, null, null)]
    public void ResolvesMembersInsideGenericValueTypeFields(string shape, int relative, int width, bool store,
        string[]? inner, string? member)
    {
        var fieldType = shape switch
        {
            "nullablePair" => Nullable(Pair(Int64, _app.SystemTypes.SystemStringType)),
            "paddedPair" => Pair(_app.SystemTypes.SystemStringType, Int16),
            "nullableIntPair" => Nullable(Pair(_app.SystemTypes.SystemInt32Type, _app.SystemTypes.SystemInt32Type)),
            _ => Pair(Int16, Int16),
        };
        var owner = Type("UnityEngine.Object");
        var field = owner.Fields.Single(f => f.Name == "m_CachedPtr");
        field.FieldType = fieldType;

        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), owner);
        var value = new LocalVariable("value", new Register(null, "value"), width == 8 ? Int64 : Int16);
        var memory = new MemoryOperand(receiver, addend: field.Offset + relative, accessSize: width);
        var access = store ? new Instruction(0, OpCode.Move, memory, value) : new Instruction(0, OpCode.Move, value, memory);
        var method = new InjectedMethodAnalysisContext(owner, "Access", _app.SystemTypes.SystemVoidType,
            MethodAttributes.Static | MethodAttributes.Public, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([access, new(1, OpCode.Return)]),
            Locals = [receiver, value], ParameterLocals = []
        };

        MetadataResolver.ResolveFieldOffsets(method);

        var operand = access.Operands[store ? 0 : 1];
        if (member == null)
        {
            Assert.That(operand, Is.InstanceOf<MemoryOperand>(), "An access reaching another member or past the container must stay unresolved");
            return;
        }

        var reference = (FieldReference)operand;
        Assert.That(reference.Field.Name, Is.EqualTo(member));
        Assert.That(reference.Field, Is.TypeOf<ConcreteGenericFieldAnalysisContext>());
        Assert.That(reference.ContainingFields.Select(f => f.Name), Is.EqualTo(new[] { field.Name }.Concat(inner!)));
        Assert.That(reference.ContainingFields.Skip(1).All(f => f is ConcreteGenericFieldAnalysisContext));
        if (member == "has_value")
            Assert.That(reference.Field.FieldType, Is.SameAs(_app.SystemTypes.SystemBooleanType));
        else if (shape == "nullablePair")
        {
            Assert.That(reference.Field.DeclaringType.FullName, Is.EqualTo(Pair(Int64, _app.SystemTypes.SystemStringType).FullName));
            Assert.That(reference.Field.FieldType, Is.SameAs(member == "key" ? Int64 : _app.SystemTypes.SystemStringType));
        }
        else
            Assert.That(reference.Field.FieldType, Is.SameAs(Int16));
    }

    [TestCase(0, "key")]
    [TestCase(8, "value")]
    [TestCase(16, null)]
    public void ResolvesGenericValueTypeReceiverFromItsUnboxedStart(int offset, string? member)
    {
        // A value-type receiver (this, a return buffer) addresses unboxed storage: no object header.
        var tuple = Pair(_app.SystemTypes.SystemInt32Type, Int64);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), tuple);
        var value = new LocalVariable("value", new Register(null, "value"));
        var store = new Instruction(0, OpCode.Move, new MemoryOperand(receiver, addend: offset), value);
        var method = new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType, "Fill", _app.SystemTypes.SystemVoidType,
            MethodAttributes.Static | MethodAttributes.Public, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([store, new(1, OpCode.Return)]),
            Locals = [receiver, value], ParameterLocals = []
        };

        MetadataResolver.ResolveFieldOffsets(method);

        if (member == null)
        {
            Assert.That(store.Operands[0], Is.InstanceOf<MemoryOperand>());
            return;
        }
        var field = ((FieldReference)store.Operands[0]).Field;
        Assert.That(field.Name, Is.EqualTo(member));
        Assert.That(field.DeclaringType, Is.SameAs(tuple));
    }
}
