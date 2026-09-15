using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class PinnedArrayRecoveryTests
{
    [TestCase(false, false)]
    [TestCase(false, true)]
    [TestCase(true, false)]
    [TestCase(true, true)]
    public void RecoversGuardedBytePointer(bool swapped, bool emptyGuard) => Check(swapped, emptyGuard, false, true);

    [TestCase(false)]
    [TestCase(true)]
    public void RejectsUnrelatedNullSelection(bool emptyGuard) => Check(false, emptyGuard, true, false);

    [Test]
    public void RecoversRawArrayLengthGuard() => Check(false, true, false, true, true);

    private static void Check(bool swapped, bool emptyGuard, bool unrelatedGuard, bool expected, bool rawLength = false)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var arrayType = new SzArrayTypeAnalysisContext(app.SystemTypes.SystemByteType);
        var array = new LocalVariable("array", new Register(null, "array"), arrayType);
        var other = new LocalVariable("other", new Register(null, "other"), arrayType);
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"), arrayType);
        var phi = new LocalVariable("phi", new Register(null, "phi"), arrayType);
        var index = new LocalVariable("index", new Register(null, "index"), app.SystemTypes.SystemIntPtrType);
        var value = new LocalVariable("value", new Register(null, "value"));
        var condition = new LocalVariable("condition", new Register(null, "condition"), app.SystemTypes.SystemBooleanType);
        var load = new Instruction(4, OpCode.Move, value, new MemoryOperand(swapped ? index : phi, swapped ? phi : index, scale: 1));
        var merge = new Instruction(3, OpCode.Phi, phi);
        IOperand checkedValue = unrelatedGuard ? other : array;
        if (emptyGuard) checkedValue = rawLength
            ? new MemoryOperand((LocalVariable)checkedValue, addend: 3 * app.Binary.PointerSizeBytes)
            : new ArrayLength((LocalVariable)checkedValue);
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Read", app.SystemTypes.SystemByteType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([
                new(0, OpCode.CheckEqual, condition, checkedValue, new Immediate(0)),
                new(1, OpCode.ConditionalJump, merge, condition),
                new(2, OpCode.Add, pointer, array, new Immediate(4 * app.Binary.PointerSizeBytes)),
                merge, load,
                new(5, OpCode.Move, new MemoryOperand(swapped ? index : phi, swapped ? phi : index, scale: 1), value),
                new(6, OpCode.Return, value)]),
            Locals = [array, other, pointer, phi, index, value, condition], ParameterLocals = []
        };
        var block = method.ControlFlowGraph.Blocks.Find(b => b.Instructions.Contains(merge))!;
        foreach (var pred in block.Predecessors)
            merge.AddOperands([pred.Instructions.Exists(i => i.Index == 2) ? pointer : emptyGuard ? new Immediate(0) : array]);
        PinnedArrayRecovery.Run(method);
        Assert.That(load.Operands[1] is ArrayAccess, Is.EqualTo(expected));
        if (expected)
        {
            var access = (ArrayAccess)load.Operands[1];
            Assert.That(access.Array, Is.SameAs(array));
            Assert.That(access.Index, Is.SameAs(index));
            Assert.That(value.Type, Is.SameAs(app.SystemTypes.SystemByteType));
            PinnedArrayRecovery.Run(method);
            Assert.That(load.Operands[1], Is.SameAs(access));
        }
    }
}
