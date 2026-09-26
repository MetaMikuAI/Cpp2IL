using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class MergedBoxRecoveryTests
{
    [TestCase("sameClass")]
    [TestCase("sameSlot")]
    [TestCase("differentClasses")]
    [TestCase("copiedIntoSharedSlot")]
    [TestCase("mistypedSlot")]
    [TestCase("dynamicClass")]
    [TestCase("instructionBeforeCall")]
    public void BoxesWhatEachPredecessorSetUp(string shape)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var int32 = app.SystemTypes.SystemInt32Type;
        var int64 = app.SystemTypes.SystemInt64Type;
        var second = shape is "differentClasses" or "copiedIntoSharedSlot" ? int64 : int32;
        LocalVariable Local(string name, TypeAnalysisContext? type = null) => new(name, new Register(null, name), type);
        var condition = Local("condition", app.SystemTypes.SystemBooleanType);
        var left = Local("left", int32);
        // The shared slot is typed by the other path; its value is the Int64 copied into it.
        var right = Local("right", shape switch { "copiedIntoSharedSlot" => int32, "mistypedSlot" => int64, _ => second });
        var wide = Local("wide", int64);
        var dynamicClass = Local("dynamicClass");
        var klass = Local("klass");
        var address = Local("address");
        var result = Local("result", app.SystemTypes.SystemObjectType);

        var rightStore = shape == "copiedIntoSharedSlot" ? new Instruction(3, OpCode.Move, right, wide) : new Instruction(3, OpCode.Move, right, new Immediate(2));
        var merge = new Instruction(5, OpCode.Phi, klass);
        var addresses = new Instruction(6, OpCode.Phi, address);
        var call = new Instruction(7, OpCode.Call, new StringLiteral("il2cpp_vm_object_box"), result, klass, address);
        var instructions = new List<Instruction>
        {
            new(0, OpCode.ConditionalJump, rightStore, condition),
            new(1, OpCode.Move, left, new Immediate(1)),
            new(2, OpCode.Jump, merge),
            rightStore,
            new(4, OpCode.Jump, merge),
            merge, addresses, call,
            new(8, OpCode.Return, result)
        };
        if (shape == "copiedIntoSharedSlot")
            instructions.Insert(0, new(9, OpCode.Move, wide, new Immediate(2)));
        if (shape == "instructionBeforeCall")
            instructions.Insert(instructions.IndexOf(call), new(9, OpCode.Move, new MemoryOperand(address), new Immediate(3)));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Box", app.SystemTypes.SystemObjectType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph(instructions),
            Locals = [condition, left, right, wide, dynamicClass, klass, address, result], ParameterLocals = []
        };
        var graph = method.ControlFlowGraph!;
        var block = graph.FindBlockByInstruction(call)!;
        var predecessors = block.Predecessors.ToList();
        var fromLeft = predecessors.Select(p => p.Instructions.Any(i => i.Destination == left)).ToList();
        Assert.That(fromLeft, Is.EquivalentTo(new[] { true, false }));
        merge.SetOperands([klass, ..fromLeft.Select(l => l ? int32 : shape == "dynamicClass" ? dynamicClass : (IOperand)second)]);
        addresses.SetOperands([address, ..fromLeft.Select(l => (IOperand)new AddressOf(l || shape == "sameSlot" ? left : right))]);

        KeyFunctionRecovery.Run(method);

        switch (shape)
        {
            case "sameClass":
                // One box of the merged value.
                Assert.That(call.OpCode, Is.EqualTo(OpCode.Box));
                Assert.That(call.Operands[1], Is.SameAs(int32));
                var merged = graph.Instructions.Single(i => i.OpCode == OpCode.Phi && i.Operands[0] == call.Operands[2]);
                Assert.That(merged.Operands.Skip(1), Is.EqualTo(fromLeft.Select(l => l ? left : right)));
                break;
            case "sameSlot":
                Assert.That(call.Operands, Is.EqualTo(new IOperand[] { result, int32, left }));
                break;
            case "differentClasses" or "copiedIntoSharedSlot":
                // Each edge boxes its own class; the call merges the objects.
                Assert.That(call.OpCode, Is.EqualTo(OpCode.Phi));
                for (var edge = 0; edge < predecessors.Count; edge++)
                {
                    var box = predecessors[edge].Instructions.Single(i => i.OpCode == OpCode.Box);
                    Assert.That(call.Operands[edge + 1], Is.SameAs(box.Operands[0]));
                    Assert.That(box.Operands[1], Is.SameAs(fromLeft[edge] ? int32 : int64));
                    Assert.That(box.Operands[2], Is.SameAs(fromLeft[edge] ? left : shape == "copiedIntoSharedSlot" ? wide : right));
                    Assert.That(predecessors[edge].Instructions[^1].OpCode, Is.EqualTo(OpCode.Jump), "The box runs before the edge is taken");
                }
                break;
            default:
                Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
                break;
        }
    }
}
