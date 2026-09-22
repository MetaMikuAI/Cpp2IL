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

    [TestCase(false, false)]
    [TestCase(false, true)]
    [TestCase(true, false)]
    [TestCase(true, true)]
    public void DoesNotUsePlaceholderOffsetsForNestedFields(bool open, bool write)
    {
        var instance = Create(_app.SystemTypes.SystemInt32Type, array: false);
        TypeAnalysisContext owner = open ? instance.GenericType : instance;
        // The count field has placeholder offset zero; Int32.m_value also has offset zero.
        // Neither justifies treating a load from the object header as count.m_value.
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), owner);
        var value = new LocalVariable("value", new Register(null, "value"), _app.SystemTypes.SystemInt32Type);
        var memory = new MemoryOperand(receiver);
        var access = write ? new Instruction(0, OpCode.Move, memory, value) : new Instruction(0, OpCode.Move, value, memory);
        var method = new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType, "UsePlaceholder", _app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([access, new(1, OpCode.Return)]),
            Locals = [receiver, value], ParameterLocals = []
        };
        Assert.That(MetadataResolver.ResolveFieldOffsets(method), Is.False);
        Assert.That(access.Operands[write ? 0 : 1], Is.EqualTo(memory));
    }

    [TestCase(false, false)]
    [TestCase(false, true)]
    [TestCase(true, false)]
    [TestCase(true, true)]
    public void StartsDerivedFieldsAfterExactMetadataBaseExtent(bool genericWrapper, bool write)
    {
        var parent = _app.AllTypes.Single(t => t.FullName == "UnityEngine.MonoBehaviour");
        var owner = Create(_app.SystemTypes.SystemStringType, array: false);
        if (genericWrapper)
        {
            var wrapper = new InjectedTypeAnalysisContext(parent.DeclaringAssembly, "Tests", "Wrapper`1", parent, TypeAttributes.Public);
            wrapper.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
                GenericParameterAttributes.None, wrapper));
            wrapper.Fields.Add(new InjectedFieldAnalysisContext("Instance", wrapper.GenericParameters[0], FieldAttributes.Static, wrapper, 0));
            owner.GenericType.BaseType = wrapper.MakeGenericInstanceType([owner.GenericType.GenericParameters[0]]);
        }
        else
            owner.GenericType.BaseType = parent;
        var start = parent.Definition!.RawSizes.instance_size;
        Assert.That(start, Is.GreaterThan(2 * _app.Binary.PointerSizeBytes));
        Assert.That(GenericInstanceFieldLayout.FindFieldAtOffset(owner, start)?.Name, Is.EqualTo("data"));
        Assert.That(GenericInstanceFieldLayout.FindFieldAtOffset(owner, start + _app.Binary.PointerSizeBytes)?.Name, Is.EqualTo("count"));
        Assert.That(GenericInstanceFieldLayout.FindFieldAtOffset(owner, 2 * _app.Binary.PointerSizeBytes), Is.Null);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), owner);
        var value = new LocalVariable("value", new Register(null, "value"));
        var memory = new MemoryOperand(receiver, addend: start);
        var access = write ? new Instruction(0, OpCode.Move, memory, value) : new Instruction(0, OpCode.Move, value, memory);
        var caller = new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType, "Caller", _app.SystemTypes.SystemVoidType,
            MethodAttributes.Static | MethodAttributes.Public, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([access, new(1, OpCode.Return)]),
            Locals = [receiver, value], ParameterLocals = []
        };
        LocalVariables.ResolveTypesAndFields(caller);
        var field = ((FieldReference)access.Operands[write ? 0 : 1]).Field;
        Assert.That(field.Name, Is.EqualTo("data"));
        Assert.That(field.DeclaringType, Is.SameAs(owner));
        Assert.That(field.FieldType, Is.SameAs(_app.SystemTypes.SystemStringType));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void ResolvesDerivedFieldAfterMetadataSizedValueTypeInBase(bool write)
    {
        var parent = _app.AllTypes.Single(t => t.FullName == "UnityEngine.Object");
        var embedded = _app.AllTypes.Single(t => t.FullName == "System.DateTime");
        var pointer = parent.Fields.Single(f => f.Name == "m_CachedPtr");
        pointer.FieldType = embedded;
        var owner = Create(_app.SystemTypes.SystemStringType, array: false);
        owner.GenericType.BaseType = parent;
        var start = parent.Definition!.RawSizes.instance_size;
        Assert.That(embedded.Definition!.RawSizes.instance_size - 2 * _app.Binary.PointerSizeBytes,
            Is.EqualTo(start - pointer.Offset));
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), owner);
        var value = new LocalVariable("value", new Register(null, "value"));
        var memory = new MemoryOperand(receiver, addend: start);
        var access = write ? new Instruction(0, OpCode.Move, memory, value) : new Instruction(0, OpCode.Move, value, memory);
        var caller = new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType, "UseEmbeddedBase", _app.SystemTypes.SystemVoidType,
            MethodAttributes.Static | MethodAttributes.Public, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([access, new(1, OpCode.Return)]),
            Locals = [receiver, value], ParameterLocals = []
        };
        LocalVariables.ResolveTypesAndFields(caller);
        var field = ((FieldReference)access.Operands[write ? 0 : 1]).Field;
        Assert.That(field.Name, Is.EqualTo("data"));
        Assert.That(field.DeclaringType, Is.SameAs(owner));
        Assert.That(field.FieldType, Is.SameAs(_app.SystemTypes.SystemStringType));
    }

    [TestCase("padding")]
    [TestCase("outOfExtent")]
    [TestCase("unknownStruct")]
    [TestCase("explicitBase")]
    [TestCase("explicitDerived")]
    [TestCase("packing")]
    [TestCase("customSize")]
    [TestCase("missingFields")]
    [TestCase("missingMetadata")]
    public void RejectsUnprovenInheritedLayouts(string problem)
    {
        var parent = _app.AllTypes.Single(t => t.FullName == "UnityEngine.Object");
        var pointer = parent.Fields.Single(f => f.Name == "m_CachedPtr");
        var start = parent.Definition!.RawSizes.instance_size;
        var owner = Create(_app.SystemTypes.SystemStringType, array: false);
        owner.GenericType.BaseType = parent;
        switch (problem)
        {
            case "padding": pointer.FieldType = _app.SystemTypes.SystemBooleanType; break;
            case "outOfExtent": pointer.Offset += _app.Binary.PointerSizeBytes; break;
            case "unknownStruct": pointer.FieldType = _app.AllTypes.Single(t => t.FullName == "System.Decimal"); break;
            case "explicitBase": parent.Attributes = (parent.Attributes & ~TypeAttributes.LayoutMask) | TypeAttributes.ExplicitLayout; break;
            case "explicitDerived": owner.GenericType.Attributes = (owner.GenericType.Attributes & ~TypeAttributes.LayoutMask) | TypeAttributes.ExplicitLayout; break;
            case "packing": parent.Definition!.Bitfield = (parent.Definition.Bitfield & ~(0xFu << 6)) | (1u << 6); break;
            case "customSize": parent.Definition!.Bitfield &= ~(1u << 11); break;
            case "missingFields": parent.Fields.Remove(pointer); break;
            case "missingMetadata":
                var synthetic = new InjectedTypeAnalysisContext(parent.DeclaringAssembly, "Tests", "UnknownBase", _app.SystemTypes.SystemObjectType, TypeAttributes.Public);
                synthetic.Fields.Add(new InjectedFieldAnalysisContext("Value", _app.SystemTypes.SystemIntPtrType, FieldAttributes.Public,
                    synthetic, 2 * _app.Binary.PointerSizeBytes));
                owner.GenericType.BaseType = synthetic;
                break;
        }
        Assert.That(GenericInstanceFieldLayout.FindFieldAtOffset(owner, start), Is.Null);
    }
}
