using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ArrayAddressRecoveryTests
{
    private ApplicationAnalysisContext _app = null!;
    private readonly List<LocalVariable> _locals = [];

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
        _locals.Clear();
    }

    private LocalVariable Local(string name, TypeAnalysisContext? type = null)
    {
        var local = new LocalVariable(name, new Register(null, name), type);
        _locals.Add(local);
        return local;
    }

    private MethodAnalysisContext Method(params Instruction[] instructions) => new InjectedMethodAnalysisContext(
        _app.SystemTypes.SystemObjectType, "Copy", _app.SystemTypes.SystemVoidType,
        MethodAttributes.Public | MethodAttributes.Static, [])
    {
        ControlFlowGraph = new ISILControlFlowGraph([.. instructions]), Locals = [.. _locals], ParameterLocals = []
    };

    [TestCase(false, false, false, true)]
    [TestCase(false, true, false, true)]
    [TestCase(true, false, true, true)]
    [TestCase(true, true, true, true)]
    [TestCase(false, false, false, false)]
    public void PreservesFieldReadAsArrayIndex(bool is32Bit, bool write, bool isStatic, bool integer)
    {
        _app.Binary.is32Bit = is32Bit;
        var owner = _app.SystemTypes.SystemObjectType;
        var type = integer ? _app.SystemTypes.SystemByteType : owner;
        var field = new InjectedFieldAnalysisContext("Index", type,
            FieldAttributes.Public | (isStatic ? FieldAttributes.Static : 0), owner, 0);
        var receiver = Local("receiver", owner);
        var index = Local("index", type);
        var array = Local("array", new SzArrayTypeAnalysisContext(_app.SystemTypes.SystemByteType));
        var address = Local("address");
        var value = Local("value");
        var memory = new MemoryOperand(address, addend: 4 * _app.Binary.PointerSizeBytes, accessSize: 1);
        var access = write ? new Instruction(3, OpCode.Move, memory, value)
            : new Instruction(3, OpCode.Move, value, memory);
        var read = new Instruction(0, OpCode.Move, index, new FieldReference(field, receiver, 0));
        var mutation = new Instruction(1, OpCode.Move, new FieldReference(field, receiver, 0), new Immediate(0));
        var method = Method(read, mutation, new(2, OpCode.Add, address, array, index), access, new(4, OpCode.Return));
        ArrayRecovery.RecoverSplitAccesses(method);
        var operand = access.Operands[write ? 0 : 1];
        Assert.That(operand, integer ? Is.TypeOf<ArrayAccess>() : Is.TypeOf<MemoryOperand>());
        if (integer)
        {
            Assert.That(((ArrayAccess)operand).Index, Is.SameAs(index), "retain the value read before the field mutation");
            Assert.That(((ArrayAccess)operand).Array, Is.SameAs(array));
            Assert.That(read.OpCode, Is.EqualTo(OpCode.Move));
        }
    }

    private (MethodAnalysisContext Method, Instruction Load, Instruction Store, LocalVariable Index) Loop(
        bool is32Bit = false, string elementKind = "reference", string mismatch = "none")
    {
        _app.Binary.is32Bit = is32Bit;
        var stride = elementKind == "short" ? 2 : _app.Binary.PointerSizeBytes;
        var header = 4 * _app.Binary.PointerSizeBytes;
        var element = elementKind == "short" ? _app.SystemTypes.SystemInt16Type : _app.SystemTypes.SystemStringType;
        var arrayType = new SzArrayTypeAnalysisContext(element);
        var source = Local("source", arrayType);
        var target = Local("target", arrayType);
        var indexInit = Local("indexInit");
        var offsetInit = Local("offsetInit");
        var index = Local("index");
        var offset = Local("offset");
        var indexNext = Local("indexNext");
        var offsetNext = Local("offsetNext");
        var scaled = Local("scaled");
        var sourceAddress = Local("sourceAddress");
        var targetAddress = Local("targetAddress");
        var value = Local("value");
        var condition = Local("condition", _app.SystemTypes.SystemBooleanType);
        var phi = new Instruction(3, OpCode.Phi, index, indexInit, indexNext);
        var offsetPhi = new Instruction(4, OpCode.Phi, offset,
            mismatch == "edges" ? offsetNext : offsetInit, mismatch == "edges" ? offsetInit : offsetNext);
        var load = new Instruction(9, OpCode.Move, value, new MemoryOperand(sourceAddress, addend: header));
        var store = new Instruction(11, OpCode.Move, new MemoryOperand(targetAddress), value);
        var exit = new Instruction(15, OpCode.Return);
        var method = Method(
            new(0, OpCode.Move, indexInit, new Immediate(0)),
            new(1, OpCode.Move, offsetInit, new Immediate(header + (mismatch == "initial" ? 1 : 0))),
            new(2, OpCode.Jump, phi), phi, offsetPhi,
            new(5, OpCode.CheckGreaterOrEqual, condition, index, new Immediate(10)),
            new(6, OpCode.ConditionalJump, exit, condition),
            new(7, elementKind == "reference" ? OpCode.ShiftLeft : OpCode.Multiply, scaled, index,
                new Immediate(elementKind == "reference" ? (is32Bit ? 2 : 3) : stride)),
            new(8, OpCode.Add, sourceAddress, source, scaled), load,
            new(10, OpCode.Add, targetAddress, is32Bit ? offset : target, is32Bit ? target : offset), store,
            new(12, OpCode.Add, indexNext, index, new Immediate(1)),
            new(13, OpCode.Add, offsetNext, offset, new Immediate(stride + (mismatch == "step" ? 1 : 0))),
            new(14, OpCode.Jump, phi), exit);
        return (method, load, store, index);
    }

    [TestCase(false, "reference")]
    [TestCase(true, "reference")]
    [TestCase(false, "short")]
    [TestCase(true, "short")]
    public void RecoversSplitLoadsAndStrengthReducedStores(bool is32Bit, string elementKind)
    {
        var (method, load, store, index) = Loop(is32Bit, elementKind);
        ArrayRecovery.RecoverSplitAccesses(method);
        Assert.That(((ArrayAccess)load.Operands[1]).Index, Is.SameAs(index));
        Assert.That(((ArrayAccess)store.Operands[0]).Index, Is.SameAs(index));
        Assert.That(index.Type, Is.SameAs(_app.SystemTypes.SystemIntPtrType));
        Assert.That(((LocalVariable)load.Destination!).Type,
            Is.SameAs(((SzArrayTypeAnalysisContext)((ArrayAccess)load.Operands[1]).Array.Type!).ElementType));
        ArrayRecovery.RecoverSplitAccesses(method);
        Assert.That(((ArrayAccess)store.Operands[0]).Index, Is.SameAs(index));
    }

    [TestCase("initial")]
    [TestCase("step")]
    [TestCase("edges")]
    public void DoesNotGuessMismatchedInductionVariables(string mismatch)
    {
        var (method, load, store, _) = Loop(mismatch: mismatch);
        ArrayRecovery.RecoverSplitAccesses(method);
        Assert.That(load.Operands[1], Is.TypeOf<ArrayAccess>());
        Assert.That(store.Operands[0], Is.TypeOf<MemoryOperand>());
    }

    [TestCase("array")]
    [TestCase("Int64")]
    [TestCase("Single")]
    public void RejectsNonNativeIndexTypes(string kind)
    {
        var (method, load, store, index) = Loop();
        index.Type = kind switch
        {
            "array" => new SzArrayTypeAnalysisContext(_app.SystemTypes.SystemStringType),
            "Int64" => _app.SystemTypes.SystemInt64Type,
            _ => _app.SystemTypes.SystemSingleType
        };
        var type = index.Type;
        ArrayRecovery.RecoverSplitAccesses(method);
        Assert.That(load.Operands[1], Is.TypeOf<MemoryOperand>());
        Assert.That(store.Operands[0], Is.TypeOf<MemoryOperand>());
        Assert.That(index.Type, Is.SameAs(type));
    }

    [TestCase(32, "Int32", 1, 1, false, true)]
    [TestCase(32, "Int32", 8, 8, true, true)]
    [TestCase(16, "Int32", 1, 1, false, false)]
    [TestCase(8, "Int32", 1, 1, false, false)]
    [TestCase(32, "UInt32", 1, 1, false, false)]
    [TestCase(32, "Int64", 1, 1, false, false)]
    [TestCase(32, "unknown", 1, 1, false, false)]
    [TestCase(32, "Int32", 1, 8, false, false)]
    [TestCase(32, "Int32", 8, 4, true, false)]
    public void RecoversOnlyValuePreservingSignedIndexExtensions(int bits, string kind, int stride, int accessSize, bool write, bool expected)
    {
        _app.Binary.is32Bit = false;
        var type = kind switch
        {
            "Int32" => _app.SystemTypes.SystemInt32Type,
            "UInt32" => _app.SystemTypes.SystemUInt32Type,
            "Int64" => _app.SystemTypes.SystemInt64Type,
            _ => null
        };
        var element = stride == 1 ? _app.SystemTypes.SystemByteType : _app.SystemTypes.SystemStringType;
        var array = Local("array", new SzArrayTypeAnalysisContext(element));
        var original = Local("original", type);
        var index = Local("index", type);
        var extended = Local("extended", _app.SystemTypes.SystemInt64Type);
        var scaled = Local("scaled", _app.SystemTypes.SystemInt64Type);
        var address = Local("address");
        var value = Local("value", element);
        var memory = new MemoryOperand(address, addend: 32, accessSize: accessSize);
        var access = write ? new Instruction(4, OpCode.Move, memory, value) : new Instruction(4, OpCode.Move, value, memory);
        var increment = new Instruction(0, OpCode.Add, index, original, new Immediate(1));
        var method = Method(increment,
            new(1, OpCode.SignExtend, extended, index, new Immediate(bits)),
            new(2, OpCode.Multiply, scaled, extended, new Immediate(stride)),
            new(3, OpCode.Add, address, array, scaled), access, new(5, OpCode.Return));
        ArrayRecovery.RecoverSplitAccesses(method);
        var operand = access.Operands[write ? 0 : 1];
        Assert.That(operand, expected ? Is.TypeOf<ArrayAccess>() : Is.TypeOf<MemoryOperand>());
        if (expected)
        {
            Assert.That(((ArrayAccess)operand).Index, Is.SameAs(index), "retain the Int32 overflow boundary");
            Assert.That(((ArrayAccess)operand).Array, Is.SameAs(array));
            Assert.That(increment.OpCode, Is.EqualTo(OpCode.Add));
        }
    }

    [TestCase(false, false)]
    [TestCase(false, true)]
    [TestCase(true, false)]
    [TestCase(true, true)]
    public void RecoversFieldLoadedIndexWithoutRereadingAfterMutation(bool is32Bit, bool write)
    {
        _app.Binary.is32Bit = is32Bit;
        var owner = new InjectedTypeAnalysisContext(_app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "Tests", "Counter", _app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var field = new InjectedFieldAnalysisContext("count", _app.SystemTypes.SystemInt32Type,
            FieldAttributes.Public, owner, 2 * _app.Binary.PointerSizeBytes);
        var receiver = Local("receiver", owner);
        var count = new FieldReference(field, receiver, field.Offset);
        var array = Local("array", new SzArrayTypeAnalysisContext(_app.SystemTypes.SystemStringType));
        var index = Local("index", _app.SystemTypes.SystemInt32Type);
        var scaled = Local("scaled");
        var address = Local("address");
        var value = Local("value", _app.SystemTypes.SystemStringType);
        var snapshot = new Instruction(0, OpCode.Move, index, count);
        var memory = new MemoryOperand(address, addend: 4 * _app.Binary.PointerSizeBytes,
            accessSize: _app.Binary.PointerSizeBytes);
        var access = write ? new Instruction(4, OpCode.Move, memory, value) : new Instruction(4, OpCode.Move, value, memory);
        var method = Method(snapshot,
            new(1, OpCode.ShiftLeft, scaled, index, new Immediate(is32Bit ? 2 : 3)),
            new(2, OpCode.Add, address, array, scaled),
            new(3, OpCode.Move, count, new Immediate(99)), access, new(5, OpCode.Return));
        ArrayRecovery.RecoverSplitAccesses(method);
        var recovered = (ArrayAccess)access.Operands[write ? 0 : 1];
        Assert.That(recovered.Array, Is.SameAs(array));
        Assert.That(recovered.Index, Is.SameAs(index), "use the captured index, not the mutated field");
        Assert.That(snapshot.Operands[1], Is.SameAs(count));
    }

    [Test]
    public void DoesNotTreatAnOffsetLoadAsAnAddressComputation()
    {
        var array = Local("array", new SzArrayTypeAnalysisContext(_app.SystemTypes.SystemStringType));
        var index = Local("index");
        var offset = Local("loadedOffset");
        var address = Local("address");
        var result = Local("result");
        var load = new Instruction(2, OpCode.Move, result, new MemoryOperand(address));
        var method = Method(
            new(0, OpCode.Move, offset, new MemoryOperand(indexRegister: index, addend: 32, scale: 8)),
            new(1, OpCode.Add, address, array, offset), load, new(3, OpCode.Return));
        ArrayRecovery.RecoverSplitAccesses(method);
        Assert.That(load.Operands[1], Is.TypeOf<MemoryOperand>());
    }

    [TestCase("Byte")]
    [TestCase("SByte")]
    [TestCase("Int16")]
    [TestCase("UInt16")]
    [TestCase("Char")]
    public void RecoveredSmallIntegerElementsCanIndexAnotherArray(string kind)
    {
        _app.Binary.is32Bit = false;
        var element = kind switch
        {
            "Byte" => _app.SystemTypes.SystemByteType,
            "SByte" => _app.SystemTypes.SystemSByteType,
            "Int16" => _app.SystemTypes.SystemInt16Type,
            "UInt16" => _app.SystemTypes.SystemUInt16Type,
            _ => _app.SystemTypes.SystemCharType
        };
        var stride = kind is "Byte" or "SByte" ? 1 : 2;
        var data = Local("data", new SzArrayTypeAnalysisContext(element));
        var table = Local("table", new SzArrayTypeAnalysisContext(_app.SystemTypes.SystemStringType));
        var index = Local("index");
        var scaled = Local("scaled");
        var value = Local("value");
        var load = new Instruction(0, OpCode.Move, index, new MemoryOperand(data, addend: 32, accessSize: stride));
        var lookup = new Instruction(2, OpCode.Move, value, new MemoryOperand(table, scaled, 32, accessSize: 8));
        var method = Method(load, new(1, OpCode.ShiftLeft, scaled, index, new Immediate(3)), lookup, new(3, OpCode.Return));
        ArrayRecovery.RecoverSplitAccesses(method);
        Assert.That(load.Operands[1], Is.TypeOf<ArrayAccess>());
        Assert.That(((ArrayAccess)lookup.Operands[1]).Index, Is.SameAs(index));
        Assert.That(index.Type, Is.SameAs(element));
        Assert.That(value.Type, Is.SameAs(_app.SystemTypes.SystemStringType));
    }

    [TestCase(32, true)]
    [TestCase(40, true)]
    [TestCase(24, false)]
    [TestCase(33, false)]
    public void RequiresAnExactElementOffset(long offset, bool expected)
    {
        var array = Local("array", new SzArrayTypeAnalysisContext(_app.SystemTypes.SystemStringType));
        var address = Local("address");
        var result = Local("result");
        var load = new Instruction(1, OpCode.Move, result, new MemoryOperand(address));
        var method = Method(new(0, OpCode.Add, address, array, new Immediate(offset)), load, new(2, OpCode.Return));
        ArrayRecovery.RecoverSplitAccesses(method);
        Assert.That(load.Operands[1], expected ? Is.TypeOf<ArrayAccess>()
            : offset == 24 ? Is.TypeOf<ArrayLength>() : Is.TypeOf<MemoryOperand>());
        if (expected)
            Assert.That(((Immediate)((ArrayAccess)load.Operands[1]).Index).Value, Is.EqualTo((offset - 32) / 8));
    }

    [TestCase(false, 0L, false)]
    [TestCase(true, 0L, false)]
    [TestCase(false, 48L, false)]
    [TestCase(true, 24L, true)]
    [TestCase(false, 0L, true)]
    [TestCase(true, 0L, true)]
    public void RecoversWholeElementBiasWithoutAPeerCounter(bool is32Bit, long offset, bool write)
    {
        _app.Binary.is32Bit = is32Bit;
        var stride = _app.Binary.PointerSizeBytes;
        var array = Local("array", new SzArrayTypeAnalysisContext(_app.SystemTypes.SystemStringType));
        var counter = Local("counter", _app.SystemTypes.SystemInt32Type);
        var value = Local("value", _app.SystemTypes.SystemStringType);
        var memory = new MemoryOperand(array, counter, offset, stride);
        var access = write ? new Instruction(0, OpCode.Move, memory, value) : new Instruction(0, OpCode.Move, value, memory);
        var method = Method(access, new(1, OpCode.Return));
        ArrayRecovery.RecoverSplitAccesses(method);
        var element = (ArrayAccess)access.Operands[write ? 0 : 1];
        var adjusted = (LocalVariable)element.Index;
        var adjustment = method.ControlFlowGraph!.Instructions.Single(i => i.Destination == adjusted);
        Assert.That(element.Array, Is.SameAs(array));
        Assert.That(adjusted.Type, Is.SameAs(counter.Type));
        Assert.That(method.Locals, Does.Contain(adjusted));
        Assert.That(adjustment.OpCode, Is.EqualTo(OpCode.Add));
        Assert.That(adjustment.Operands[1], Is.SameAs(counter));
        Assert.That(((Immediate)adjustment.Operands[2]).Value, Is.EqualTo(offset / stride - 4));
        var instructions = method.ControlFlowGraph.Instructions.ToList();
        Assert.That(instructions.IndexOf(adjustment), Is.LessThan(instructions.IndexOf(access)));
        ArrayRecovery.RecoverSplitAccesses(method);
        Assert.That(method.ControlFlowGraph.Instructions.Count(), Is.EqualTo(instructions.Count));
    }

    [TestCase(1L, 8)]
    [TestCase(0L, 4)]
    [TestCase(0x4000000020L, 8)]
    public void DoesNotGuessMisalignedWrongStrideOrOversizedBias(long offset, int stride)
    {
        var array = Local("array", new SzArrayTypeAnalysisContext(_app.SystemTypes.SystemStringType));
        var counter = Local("counter");
        var value = Local("value");
        var access = new Instruction(0, OpCode.Move, value, new MemoryOperand(array, counter, offset, stride));
        var method = Method(access, new(1, OpCode.Return));
        ArrayRecovery.RecoverSplitAccesses(method);
        Assert.That(access.Operands[1], Is.TypeOf<MemoryOperand>());
        Assert.That(counter.Type, Is.Null);
        Assert.That(method.Locals.Count, Is.EqualTo(3));
    }


    [TestCase(false, false, false)]
    [TestCase(true, false, false)]
    [TestCase(false, true, false)]
    [TestCase(true, true, false)]
    [TestCase(false, false, true)]
    [TestCase(true, true, true)]
    public void RecoversLengthThroughInteriorPointers(bool is32Bit, bool allocated, bool structElement)
    {
        _app.Binary.is32Bit = is32Bit;
        var pointerSize = _app.Binary.PointerSizeBytes;
        var element = structElement ? _app.AllTypes.Single(t => t.FullName == "System.Decimal") : _app.SystemTypes.SystemStringType;
        var arrayType = new SzArrayTypeAnalysisContext(element);
        var array = Local("array", allocated ? null : arrayType);
        var first = Local("first");
        var second = Local("second");
        var length = Local("length");
        var allocation = allocated ? new Instruction(0, OpCode.Call, new StringLiteral("SzArrayNew"), array, arrayType, new Immediate(10))
            : new Instruction(0, OpCode.Nop);
        var load = new Instruction(3, OpCode.Move, length, new MemoryOperand(second, addend: -3 * pointerSize));
        var method = Method(allocation,
            new(1, OpCode.Add, first, array, new Immediate(4 * pointerSize)),
            new(2, OpCode.Add, second, first, new Immediate(2 * pointerSize)),
            load, new(4, OpCode.Return, length));
        ArrayRecovery.RecoverSplitAccesses(method);
        Assert.That(((ArrayLength)load.Operands[1]).Array, Is.SameAs(array));
        Assert.That(length.Type, Is.SameAs(_app.SystemTypes.SystemInt32Type));
        if (allocated) Assert.That(allocation.OpCode, Is.EqualTo(OpCode.NewArr));
        ArrayRecovery.RecoverSplitAccesses(method);
        DeadCodeEliminator.Run(method);
        Assert.That(method.ControlFlowGraph!.Instructions.Any(i => i.OpCode == OpCode.Add), Is.False);
        Assert.That(load.Operands[1], Is.TypeOf<ArrayLength>());
    }

    [TestCase("store")]
    [TestCase("offset")]
    [TestCase("index")]
    [TestCase("unknownArray")]
    [TestCase("ambiguousAddress")]
    public void DoesNotGuessHeaderAccesses(string shape)
    {
        var array = Local("array", shape == "unknownArray" ? null : new SzArrayTypeAnalysisContext(_app.SystemTypes.SystemStringType));
        var address = Local("address");
        var result = Local("result");
        var memory = new MemoryOperand(address, shape == "index" ? Local("index") : null, shape == "offset" ? -7 : -8);
        var access = shape == "store" ? new Instruction(2, OpCode.Move, memory, result) : new Instruction(2, OpCode.Move, result, memory);
        var method = Method(new(0, OpCode.Add, address, array, new Immediate(32)),
            shape == "ambiguousAddress" ? new(1, OpCode.Move, address, new Immediate(0)) : new(1, OpCode.Nop),
            access, new(3, OpCode.Return));
        ArrayRecovery.RecoverSplitAccesses(method);
        Assert.That(access.Operands[shape == "store" ? 0 : 1], Is.TypeOf<MemoryOperand>());
    }

    [TestCase(false)]
    [TestCase(true)]
    public void PropagatesRecoveredLengthThroughCopiesAndArithmeticWithoutGuessingPointers(bool is32Bit)
    {
        _app.Binary.is32Bit = is32Bit;
        var pointerSize = _app.Binary.PointerSizeBytes;
        var array = Local("array", new SzArrayTypeAnalysisContext(_app.SystemTypes.SystemStringType));
        var address = Local("address");
        var length = Local("length");
        var copy = Local("copy");
        var difference = Local("difference");
        var unknown = Local("unknown");
        var ambiguous = Local("ambiguous");
        var existing = Local("existing", _app.SystemTypes.SystemObjectType);
        var method = Method(
            new(0, OpCode.Add, address, array, new Immediate(4 * pointerSize)),
            new(1, OpCode.Move, length, new MemoryOperand(address, addend: -pointerSize)),
            new(2, OpCode.Move, copy, length),
            new(3, OpCode.Subtract, difference, copy, new Immediate(1)),
            new(4, OpCode.Add, ambiguous, difference, unknown),
            new(5, OpCode.Add, existing, difference, new Immediate(1)),
            new(6, OpCode.Return, difference));
        ArrayRecovery.RecoverSplitAccesses(method);
        Assert.That(difference.Type, Is.Null, "Array recovery alone does not propagate downstream types");
        LocalVariables.PropagateKnownTypes(method);
        Assert.That(copy.Type, Is.SameAs(_app.SystemTypes.SystemInt32Type));
        Assert.That(difference.Type, Is.SameAs(_app.SystemTypes.SystemInt32Type));
        Assert.That(address.Type, Is.Null);
        Assert.That(ambiguous.Type, Is.Null);
        Assert.That(unknown.Type, Is.Null);
        Assert.That(existing.Type, Is.SameAs(_app.SystemTypes.SystemObjectType));
        var types = method.Locals.Select(l => l.Type).ToArray();
        LocalVariables.PropagateKnownTypes(method);
        Assert.That(method.Locals.Select(l => l.Type), Is.EqualTo(types));
    }
}
