using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class GenericStaticFieldRecoveryTests
{
    private ApplicationAnalysisContext _app = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
    }

    private (MethodAnalysisContext Method, Instruction Access, Instruction ClassLoad, Instruction StorageLoad,
        GenericInstanceTypeAnalysisContext Owner, LocalVariable Value) Create(bool valueArgument = false,
        bool write = false, string shape = "single", long accessOffset = 0)
    {
        var root = _app.SystemTypes.SystemObjectType;
        var definition = new InjectedTypeAnalysisContext(root.DeclaringAssembly, "Tests", "Storage`1", root, TypeAttributes.Public);
        var parameter = new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            GenericParameterAttributes.None, definition);
        definition.GenericParameters.Add(parameter);
        var fieldType = new SzArrayTypeAnalysisContext(parameter);
        var attributes = FieldAttributes.Public | FieldAttributes.Static;
        var offset = shape == "threadStatic" ? -1 : shape == "nonzero" ? 8 : 0;
        // A static field sized by the type argument makes every later offset instantiation-dependent.
        if (shape == "sizedByArgument")
            definition.Fields.Add(new InjectedFieldAnalysisContext("Sized", parameter, FieldAttributes.Public | FieldAttributes.Static, definition, 0));
        definition.Fields.Add(new InjectedFieldAnalysisContext("Value", fieldType,
            shape == "literalOnly" ? attributes | FieldAttributes.Literal : attributes, definition, offset));
        if (shape is "ambiguous" or "distinctOffsets")
            definition.Fields.Add(new InjectedFieldAnalysisContext("Other", fieldType, attributes, definition,
                shape == "distinctOffsets" ? 8 : 0));
        if (shape == "constant")
            definition.Fields.Add(new InjectedFieldAnalysisContext("Constant", _app.SystemTypes.SystemInt32Type,
                attributes | FieldAttributes.Literal, definition, 0, 1));
        if (shape == "instance")
            definition.Fields.Add(new InjectedFieldAnalysisContext("InstanceValue", root, FieldAttributes.Public,
                definition, 16));
        var argument = valueArgument ? _app.SystemTypes.SystemInt32Type : root;
        var owner = definition.MakeGenericInstanceType([argument]);
        var klass = new LocalVariable("klass", new Register(null, "klass"));
        var storage = new LocalVariable("storage", new Register(null, "storage"));
        var value = new LocalVariable("value", new Register(null, "value"), write ? new SzArrayTypeAnalysisContext(argument) : null);
        var classLoad = new Instruction(0, OpCode.Move, klass, owner);
        var storageLoad = new Instruction(1, OpCode.Move, storage,
            new MemoryOperand(klass, addend: _app.Binary.is32Bit ? 0x5C : 0xB8));
        var memory = new MemoryOperand(storage, addend: accessOffset);
        var access = write ? new Instruction(2, OpCode.Move, memory, value) : new Instruction(2, OpCode.Move, value, memory);
        var method = new InjectedMethodAnalysisContext(root, "UseStorage", _app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([classLoad, storageLoad, access,
                new(3, OpCode.CallVoid, new StringLiteral("consume"), value), new(4, OpCode.Return)]),
            Locals = [klass, storage, value], ParameterLocals = []
        };
        return (method, access, classLoad, storageLoad, owner, value);
    }

    [TestCase(false, false, false)]
    [TestCase(false, true, false)]
    [TestCase(true, false, false)]
    [TestCase(true, true, false)]
    [TestCase(false, false, true)]
    [TestCase(true, false, true)]
    public void ResolvesConcreteStaticFieldAndRemovesRuntimePointerLoads(bool valueArgument, bool write, bool is32Bit)
    {
        _app.Binary.is32Bit = is32Bit;
        var (method, access, classLoad, storageLoad, owner, value) = Create(valueArgument, write);
        LocalVariables.ResolveTypesAndFields(method);
        var field = (FieldReference)access.Operands[write ? 0 : 1];
        Assert.That(field.Field, Is.TypeOf<ConcreteGenericFieldAnalysisContext>());
        Assert.That(field.Field.IsStatic, Is.True);
        Assert.That(field.Field.DeclaringType, Is.SameAs(owner));
        Assert.That(((SzArrayTypeAnalysisContext)field.Field.FieldType).ElementType, Is.SameAs(owner.GenericArguments[0]));
        Assert.That(((SzArrayTypeAnalysisContext)value.Type!).ElementType, Is.SameAs(owner.GenericArguments[0]));
        Assert.That(MetadataResolver.ResolveFieldOffsets(method), Is.False, "Resolution should be idempotent");
        DeadCodeEliminator.Run(method);
        Assert.That(classLoad.OpCode, Is.EqualTo(OpCode.Nop));
        Assert.That(storageLoad.OpCode, Is.EqualTo(OpCode.Nop));
        Assert.That(access.OpCode, Is.EqualTo(OpCode.Move));
    }

    [TestCase("constant")]
    [TestCase("instance")]
    public void IgnoresFieldsThatDoNotUseStaticStorage(string shape)
    {
        var (method, access, _, _, _, _) = Create(shape: shape);
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(access.Operands[1], Is.TypeOf<FieldReference>());
    }

    // IL2CPP lays static fields out in declaration order at their natural alignment, so with sizes that do
    // not depend on the type argument each field's offset is the same in every instantiation, whatever
    // placeholder offsets the generic definition reports.
    [TestCase("ambiguous", 0, "Value")]
    [TestCase("ambiguous", 8, "Other")]
    [TestCase("distinctOffsets", 0, "Value")]
    [TestCase("distinctOffsets", 8, "Other")]
    public void ComputesStaticLayoutOfSeveralFields(string shape, long accessOffset, string expected)
    {
        var (method, access, _, _, _, _) = Create(shape: shape, accessOffset: accessOffset);
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(access.Operands[1], Is.TypeOf<FieldReference>());
        Assert.That(((FieldReference)access.Operands[1]).Field.Name, Is.EqualTo(expected));
    }

    [TestCase("sizedByArgument", 8)]
    [TestCase("literalOnly", 0)]
    [TestCase("threadStatic", 0)]
    [TestCase("nonzero", 8)]
    [TestCase("single", 8)]
    public void DoesNotGuessUnsupportedStaticLayouts(string shape, long accessOffset)
    {
        var (method, access, _, storageLoad, _, _) = Create(shape: shape, accessOffset: accessOffset);
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(access.Operands[1], Is.TypeOf<MemoryOperand>());
        DeadCodeEliminator.Run(method);
        Assert.That(storageLoad.OpCode, Is.EqualTo(OpCode.Move));
    }
}
