using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ArrayStoreCheckRecoveryTests
{
    [TestCase("store", true)]
    [TestCase("indexedStore", true)]
    [TestCase("otherValue", false)]
    [TestCase("otherArray", false)]
    [TestCase("callBeforeStore", false)]
    [TestCase("otherFailure", false)]
    [TestCase("resultReused", false)]
    [TestCase("joinMergesOtherValues", true)]
    public void RemovesOnlyTheCheckOfAFollowingStore(string shape, bool expected)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var element = app.SystemTypes.SystemStringType;
        var arrayType = new SzArrayTypeAnalysisContext(element);
        var exceptionType = app.AllTypes.First(t => t.FullName == (shape == "otherFailure"
            ? "System.InvalidOperationException" : "System.ArrayTypeMismatchException"));
        LocalVariable Local(string name, TypeAnalysisContext? type = null) => new(name, new Register(null, name), type);
        Instruction? phiToFill = null;
        var array = Local("array", arrayType);
        var other = Local("other", arrayType);
        var value = Local("value", element);
        var index = Local("index", app.SystemTypes.SystemInt64Type);
        var klass = Local("klass");
        var elementClass = Local("elementClass");
        var isNull = Local("isNull", app.SystemTypes.SystemBooleanType);
        var result = Local("result");
        var failed = Local("failed", app.SystemTypes.SystemBooleanType);
        var address = Local("address");
        var exception = Local("exception", exceptionType);

        var call = new Instruction(4, OpCode.Call, new StringLiteral("il2cpp_vm_object_is_inst"), result, value, elementClass);
        var computeAddress = new Instruction(7, OpCode.Add, address, shape == "otherArray" ? other : array, shape == "indexedStore" ? index : new Immediate(0x28));
        var store = new Instruction(8, OpCode.Move, new MemoryOperand(address), shape == "otherValue" ? other : value);
        var fail = new Instruction(10, OpCode.Newobj, exception, exceptionType);
        var instructions = new List<Instruction>
        {
            new(0, OpCode.CheckEqual, isNull, value, new Immediate(0)),
            new(1, OpCode.ConditionalJump, computeAddress, isNull),
            new(2, OpCode.Move, klass, new MemoryOperand(array)),
            new(3, OpCode.Move, elementClass, new MemoryOperand(klass, addend: 0x40)),
            call,
            new(5, OpCode.CheckEqual, failed, result, new Immediate(0)),
            new(6, OpCode.ConditionalJump, fail, failed),
            computeAddress, store,
            new(9, OpCode.Return),
            fail, new(11, OpCode.Throw, exception)
        };
        if (shape == "callBeforeStore")
            instructions.Insert(instructions.IndexOf(store), new(12, OpCode.CallVoid, new Immediate(0x1234), value));
        if (shape == "resultReused")
            instructions.Insert(instructions.IndexOf(store), new(12, OpCode.Move, new MemoryOperand(other), result));
        // The join merges the index for the null path but the array for the checked one: the null
        // test decides a live value, so it must stay although the check itself goes.
        var merged = Local("merged");
        if (shape == "joinMergesOtherValues")
        {
            var phi = new Instruction(12, OpCode.Phi, merged);
            instructions.Insert(instructions.IndexOf(computeAddress), phi);
            instructions[1].SetOperand(0, phi);
            instructions.Insert(instructions.IndexOf(store) + 1, new(13, OpCode.Move, new MemoryOperand(other), merged));
            phiToFill = phi;
        }
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Store", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph(instructions),
            Locals = [array, other, value, index, klass, elementClass, isNull, result, failed, address, exception, merged], ParameterLocals = []
        };
        if (phiToFill != null)
        {
            var join = method.ControlFlowGraph!.FindBlockByInstruction(phiToFill)!;
            phiToFill.SetOperands([merged, ..join.Predecessors.Select(p => p.Instructions.Any(i => i.Index == 1) ? (IOperand)index : array)]);
        }

        KeyFunctionRecovery.Run(method);

        var graph = method.ControlFlowGraph!;
        Assert.That(call.OpCode, Is.EqualTo(expected ? OpCode.Nop : OpCode.Call));
        Assert.That(graph.Instructions.Any(i => i.OpCode == OpCode.Throw), Is.EqualTo(!expected), "The failure path goes with the check");
        if (!expected)
            return;
        // The null test only guarded the check, so the store is now reached unconditionally.
        Assert.That(graph.Instructions.Any(i => i.OpCode == OpCode.ConditionalJump), Is.EqualTo(shape == "joinMergesOtherValues"));
        Assert.That(graph.Instructions.Any(i => i.Operands.Contains(klass) || i.Operands.Contains(elementClass)), Is.False);
        Assert.That(store.Operands[1], Is.SameAs(value));
    }
}
