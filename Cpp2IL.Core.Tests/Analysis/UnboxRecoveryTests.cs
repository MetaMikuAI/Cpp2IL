using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class UnboxRecoveryTests
{
    [TestCase("elementClass", true, true)]
    [TestCase("exactClass", true, false)]
    [TestCase("isInstance", true, false)]
    [TestCase("constantPhi", true, true)]
    [TestCase("callBeforeUnbox", true, false)]
    [TestCase("mergedThrow", true, true)]
    [TestCase("loadBeforeThrow", true, false)]
    [TestCase("narrowLoad", false, false)]
    [TestCase("otherObject", false, false)]
    [TestCase("unguarded", false, false)]
    [TestCase("referenceType", false, false)]
    [TestCase("mistypedValue", false, false)]
    public void UnboxesOnlyTheTypeADominatingClassTestProves(string shape, bool expected, bool guardRemoved)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var int32 = app.SystemTypes.SystemInt32Type;
        var checkedType = shape == "referenceType" ? app.SystemTypes.SystemStringType : int32;
        var invalidCast = app.AllTypes.First(t => t.FullName == "System.InvalidCastException");
        LocalVariable Local(string name, TypeAnalysisContext? type = null) => new(name, new Register(null, name), type);
        var boxed = Local("boxed", app.SystemTypes.SystemObjectType);
        var other = Local("other", app.SystemTypes.SystemObjectType);
        var klass = Local("klass");
        var element = Local("element");
        var expectedClass = Local("expectedClass");
        var expectedElement = Local("expectedElement");
        var differs = Local("differs", app.SystemTypes.SystemBooleanType);
        var pointer = Local("pointer");
        var value = Local("value", shape == "mistypedValue" ? app.SystemTypes.SystemInt64Type : int32);

        var guarded = shape == "otherObject" ? other : boxed;
        var call = new Instruction(6, OpCode.Call, new StringLiteral("il2cpp_vm_object_unbox"), pointer, boxed);
        var load = new Instruction(7, OpCode.Move, value, new MemoryOperand(pointer, accessSize: shape == "narrowLoad" ? 2 : 4));
        var fail = new Instruction(9, OpCode.Throw, invalidCast);
        IOperand classConstant = shape == "constantPhi" ? expectedClass : checkedType;
        var test = shape switch
        {
            "exactClass" => new Instruction(4, OpCode.CheckNotEqual, differs, klass, checkedType),
            "isInstance" => new Instruction(4, OpCode.CheckEqual, differs, element, new Immediate(0)),
            _ => new Instruction(4, OpCode.CheckNotEqual, differs, element, expectedElement)
        };
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, klass, new MemoryOperand(guarded)),
            shape == "isInstance" ? new(1, OpCode.IsInstance, element, checkedType, guarded) : new(1, OpCode.Move, element, new MemoryOperand(klass, addend: 0x40)),
            shape == "constantPhi" ? new(2, OpCode.Phi, expectedClass, checkedType, checkedType) : new(2, OpCode.Move, expectedClass, checkedType),
            new(3, OpCode.Move, expectedElement, new MemoryOperand(expectedClass, addend: 0x40)),
            test,
            new(5, OpCode.ConditionalJump, fail, differs),
            call, load,
            new(8, OpCode.Return, value),
            fail
        };
        if (shape == "unguarded")
        {
            instructions.RemoveRange(0, 6);
            instructions.Remove(fail);
        }
        // A tail-merged throw block can merge and copy values before throwing, and keep lifted code after it.
        var merged = Local("merged");
        var copied = Local("copied");
        if (shape is "mergedThrow" or "loadBeforeThrow")
        {
            var entry = shape == "mergedThrow" ? new Instruction(11, OpCode.Phi, merged, boxed) : new Instruction(11, OpCode.Move, merged, new MemoryOperand(boxed));
            instructions.Insert(instructions.IndexOf(fail), entry);
            instructions.Insert(instructions.IndexOf(fail), new(12, OpCode.Move, copied, merged));
            instructions.Add(new(13, OpCode.Return, copied));
            instructions.Single(i => i.Index == 5).SetOperand(0, entry);
        }
        if (shape == "callBeforeUnbox")
            instructions.Insert(instructions.IndexOf(call), new(10, OpCode.CallVoid, new Immediate(0x1234), boxed));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Unbox", int32,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph(instructions),
            Locals = [boxed, other, klass, element, expectedClass, expectedElement, differs, pointer, value, merged, copied], ParameterLocals = []
        };

        KeyFunctionRecovery.Run(method);

        Assert.That(call.OpCode, Is.EqualTo(expected ? OpCode.Unbox : OpCode.Call));
        if (expected)
        {
            Assert.That(call.Operands, Is.EqualTo(new IOperand[] { value, int32, boxed }));
            Assert.That(load.OpCode, Is.EqualTo(OpCode.Nop), "unbox.any yields the value the load read");
        }
        // Only the element-class check is unbox.any's own; a class test written in the source stays.
        // (A test phi without matching predecessors defers the pruning, leaving the branch constant.)
        var graph = method.ControlFlowGraph!;
        if (shape != "unguarded")
            Assert.That(!graph.Instructions.Contains(fail) || instructions.Single(i => i.Index == 5) is { OpCode: OpCode.ConditionalJump, Operands: [_, Immediate] },
                Is.EqualTo(guardRemoved));
    }
}
