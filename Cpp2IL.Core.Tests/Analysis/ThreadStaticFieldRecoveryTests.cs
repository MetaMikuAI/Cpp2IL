using System;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ThreadStaticFieldRecoveryTests
{
    private ApplicationAnalysisContext _app = null!;
    private ulong _helper;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2022Game();
        _app.InstructionSet = new NewArmV8InstructionSet();
        _helper = _app.Binary.GetVirtualAddressOfPrimaryExecutableSection();
        _app.Binary.BaseStream.Position = _app.Binary.MapVirtualAddressToRaw(_helper);
        _app.Binary.BaseStream.Write(BitConverter.GetBytes(0xB9411400u));
        _app.Binary.BaseStream.Write(BitConverter.GetBytes(0x14000008u));
    }

    [TestCase(0xB9411400u, 0x14000008u, true)]
    [TestCase(0xB9411400u, 0x17FFFFF8u, true)]
    [TestCase(0xB9411401u, 0x14000008u, false)] // wrong destination register
    [TestCase(0xB9411420u, 0x14000008u, false)] // wrong class register
    [TestCase(0xB9400000u, 0x14000008u, false)] // wrong class field
    [TestCase(0xB9411400u, 0x94000008u, false)] // BL is not a tail call
    [TestCase(0xB9411400u, 0x54000080u, false)] // conditional branch
    [TestCase(0xB9411400u, 0xD65F03C0u, false)] // return
    [TestCase(0xB9411400u, 0x14000000u, false)] // self-loop
    [TestCase(0xB9411400u, 0x17FFFFFFu, false)] // loops back to the load
    public void RequiresExactLookupWrapper(uint load, uint branch, bool expected)
        => Assert.That(ThreadStaticFieldRecovery.IsLookupThunk(load, branch, 0x1000), Is.EqualTo(expected));

    private (MethodAnalysisContext Method, Instruction Call, Instruction Access, Instruction ClassLoad,
        TypeAnalysisContext Owner, LocalVariable Storage) Create(bool write = false, long offset = 0, bool escape = false)
    {
        var root = _app.SystemTypes.SystemObjectType;
        var owner = new InjectedTypeAnalysisContext(root.DeclaringAssembly, "Tests", "ThreadStorage", root, TypeAttributes.Public);
        var bytes = new SzArrayTypeAnalysisContext(_app.SystemTypes.SystemByteType);
        owner.Fields.Add(new InjectedFieldAnalysisContext("Buffer", bytes, FieldAttributes.Static | FieldAttributes.Private, owner, int.MinValue));
        owner.Fields.Add(new InjectedFieldAnalysisContext("OtherThreadBuffer", bytes, FieldAttributes.Static | FieldAttributes.Private, owner, int.MinValue + 8));
        owner.Fields.Add(new InjectedFieldAnalysisContext("OrdinaryBuffer", bytes, FieldAttributes.Static | FieldAttributes.Private, owner, 0));
        var klass = new LocalVariable("klass", new Register(null, "klass"));
        var storage = new LocalVariable("storage", new Register(null, "storage"));
        var value = new LocalVariable("value", new Register(null, "value"), write ? bytes : null);
        var junk = new LocalVariable("junk", new Register(null, "junk"));
        var classLoad = new Instruction(0, OpCode.Move, klass, owner);
        var call = new Instruction(1, OpCode.Call, new Immediate(unchecked((long)_helper)), storage, klass, junk);
        var memory = new MemoryOperand(storage, addend: offset);
        var access = write ? new Instruction(2, OpCode.Move, memory, value) : new Instruction(2, OpCode.Move, value, memory);
        var method = new InjectedMethodAnalysisContext(root, "UseThreadStorage", _app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([classLoad, call, access,
                new(3, OpCode.CallVoid, new StringLiteral("consume"), escape ? storage : value), new(4, OpCode.Return)]),
            Locals = [klass, storage, value, junk], ParameterLocals = []
        };
        return (method, call, access, classLoad, owner, storage);
    }

    [TestCase(false, 0)]
    [TestCase(true, 0)]
    [TestCase(false, 8)]
    [TestCase(true, 8)]
    public void ResolvesThreadFieldsWithoutConfusingOrdinaryStaticStorage(bool write, long offset)
    {
        var (method, call, access, classLoad, owner, storage) = Create(write, offset);
        KeyFunctionRecovery.Run(method);
        Assert.That(((StaticFieldStorageTypeAnalysisContext)storage.Type!).IsThreadStatic, Is.True);
        Assert.That(call.Operands.Count, Is.EqualTo(3));
        // A lookup stays until its raw address uses have been resolved.
        DeadCodeEliminator.Run(method);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
        LocalVariables.ResolveTypesAndFields(method);
        var field = (FieldReference)access.Operands[write ? 0 : 1];
        Assert.That(field.Field, Is.SameAs(owner.Fields[offset == 0 ? 0 : 1]));
        Assert.That(field.Field.IsStatic, Is.True);
        Assert.That(field.Field.FieldType, Is.TypeOf<SzArrayTypeAnalysisContext>());
        DeadCodeEliminator.Run(method);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Nop));
        Assert.That(classLoad.OpCode, Is.EqualTo(OpCode.Nop));
        KeyFunctionRecovery.Run(method);
        Assert.That(MetadataResolver.ResolveFieldOffsets(method), Is.False);
    }

    [TestCase(false)]
    [TestCase(true)]
    public void KeepsLookupWhenPointerStillHasNativeUses(bool escape)
    {
        var (method, call, access, _, _, _) = Create(offset: escape ? 0 : 4, escape: escape);
        KeyFunctionRecovery.Run(method);
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(access.Operands[1], escape ? Is.TypeOf<FieldReference>() : Is.TypeOf<MemoryOperand>());
        DeadCodeEliminator.Run(method);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
    }

    [TestCase("ordinary")]
    [TestCase("unknown")]
    [TestCase("instance")]
    [TestCase("literal")]
    public void RequiresThreadStaticFieldMetadata(string kind)
    {
        var (method, call, _, _, owner, storage) = Create();
        var type = owner.Fields[0].FieldType;
        owner.Fields.Clear();
        owner.Fields.Add(new InjectedFieldAnalysisContext("NotThreadStatic", type,
            kind == "instance" ? FieldAttributes.Public : FieldAttributes.Static | (kind == "literal" ? FieldAttributes.Literal : 0),
            owner, kind == "ordinary" ? 0 : kind == "unknown" ? -1 : int.MinValue));
        KeyFunctionRecovery.Run(method);
        Assert.That(storage.Type, Is.Null);
        Assert.That(call.Operands.Count, Is.EqualTo(4));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void DoesNotTrustDynamicClassTypesOrMixedPhis(bool mixed)
    {
        var (method, call, _, classLoad, owner, storage) = Create();
        var klass = (LocalVariable)classLoad.Destination!;
        klass.Type = new RuntimeClassTypeAnalysisContext(owner, owner.DeclaringAssembly);
        classLoad.OpCode = mixed ? OpCode.Phi : OpCode.Move;
        if (mixed)
            classLoad.SetOperands(klass, owner, _app.SystemTypes.SystemObjectType);
        else
            classLoad.SetOperands(klass, new MemoryOperand(new LocalVariable("dynamic", new Register(null, "dynamic"))));
        KeyFunctionRecovery.Run(method);
        Assert.That(storage.Type, Is.Null);
        Assert.That(call.Operands.Count, Is.EqualTo(4));
    }

    [Test]
    public void DoesNotRemoveUnrecognizedCallsWithAStorageTypedResult()
    {
        var (method, call, _, _, _, _) = Create();
        KeyFunctionRecovery.Run(method);
        LocalVariables.ResolveTypesAndFields(method);
        call.SetOperand(0, new Immediate(unchecked((long)_helper + 4)));
        DeadCodeEliminator.Run(method);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
    }

    [Test]
    public void RejectsOlderClassLayoutsEvenWithMatchingBytes()
    {
        Cpp2IlApi.ResetInternalState();
        var old = TestGameLoader.LoadSimple2019Game();
        old.InstructionSet = new NewArmV8InstructionSet();
        var address = old.Binary.GetVirtualAddressOfPrimaryExecutableSection();
        old.Binary.BaseStream.Position = old.Binary.MapVirtualAddressToRaw(address);
        old.Binary.BaseStream.Write(BitConverter.GetBytes(0xB9411400u));
        old.Binary.BaseStream.Write(BitConverter.GetBytes(0x14000008u));
        Assert.That(ThreadStaticFieldRecovery.IsLookup(old, address), Is.False);
    }

    [Test]
    public void RejectsUnsupportedArchitectureAndUnmappedAddresses()
    {
        Assert.That(ThreadStaticFieldRecovery.IsLookup(_app, _helper), Is.True);
        Assert.That(ThreadStaticFieldRecovery.IsLookup(_app, ulong.MaxValue), Is.False);
        _app.Binary.is32Bit = true;
        Assert.That(ThreadStaticFieldRecovery.IsLookup(_app, _helper), Is.False);
        _app.Binary.is32Bit = false;
        _app.InstructionSet = new X86InstructionSet();
        Assert.That(ThreadStaticFieldRecovery.IsLookup(_app, _helper), Is.False);
    }
}
