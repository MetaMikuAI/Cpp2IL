using System.Collections.Generic;
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
        Assert.That(load.Operands[1], expected ? Is.TypeOf<ArrayAccess>() : Is.TypeOf<MemoryOperand>());
        if (expected)
            Assert.That(((Immediate)((ArrayAccess)load.Operands[1]).Index).Value, Is.EqualTo((offset - 32) / 8));
    }
}
