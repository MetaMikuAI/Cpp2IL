using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterfaceDispatchSharedTests
{
    private sealed class Lookup
    {
        public required Instruction Head;
        public required Instruction Fast;
        public required Instruction SlowCall;
        public required Instruction InvokePhi;
        public required Instruction CarriedPhi;
        public required LocalVariable Merged;
        public required LocalVariable FastEntry;
        public required LocalVariable SlowResult;
        public required LocalVariable Klass;
        public required LocalVariable Carried;
        public required LocalVariable Target;
        public required LocalVariable Hidden;
        public List<Instruction> Body = [];
    }

    // Two lookups on different paths feed one indirect call through phis of their methodPtr and method loads,
    // which is how native compilers merge identical interface calls.
    [TestCase("same", true)]
    [TestCase("otherInterface", false)]
    [TestCase("carriedTwoValues", true)]
    public void RecoversMergedInterfaceCalls(string shape, bool resolved)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        app.InstructionSet = new NewArmV8InstructionSet();
        var objectType = app.SystemTypes.SystemObjectType;
        var disposable = app.AllTypes.Single(t => t.FullName == "System.IDisposable");
        var dispose = disposable.Methods.Single(m => m.Name == "Dispose");
        var enumerator = app.AllTypes.Single(t => t.FullName == "System.Collections.IEnumerator");
        var moveNext = enumerator.Methods.Single(m => m.Name == "MoveNext");
        var locals = new List<LocalVariable>();
        LocalVariable Local(string name, TypeAnalysisContext? type = null)
        {
            var local = new LocalVariable(name, new Register(null, name), type);
            locals.Add(local);
            return local;
        }

        var receiver = Local("receiver", objectType);
        var pick = Local("pick", app.SystemTypes.SystemBooleanType);
        var join = new Instruction(90, OpCode.Phi, Local("target"));
        var hiddenJoin = new Instruction(91, OpCode.Phi, Local("hidden"));
        var result = Local("result");
        var dispatch = new Instruction(92, OpCode.IndirectCall, join.Operands[0], result, receiver, hiddenJoin.Operands[0]);

        Lookup Build(string name, int baseIndex, TypeAnalysisContext iface, int slot)
        {
            var klass = Local(name + "Klass");
            var ifaceLocal = Local(name + "Iface");
            var condition = Local(name + "Condition", app.SystemTypes.SystemBooleanType);
            var offset = Local(name + "Offset");
            var indexed = Local(name + "Indexed");
            var scaled = Local(name + "Scaled");
            var sum = Local(name + "Sum");
            var fastEntry = Local(name + "Fast");
            var slotLocal = Local(name + "Slot");
            var slowResult = Local(name + "Slow");
            var merged = Local(name + "Merged");
            var carried = Local(name + "Carried");
            var target = Local(name + "Target");
            var hidden = Local(name + "Hidden");
            var slowStart = new Instruction(baseIndex + 20, OpCode.Move, slotLocal, new Immediate(slot));
            var fast = new Instruction(baseIndex + 10, OpCode.Move, offset, new MemoryOperand(klass, addend: 0xB0));
            var invokePhi = new Instruction(baseIndex + 30, OpCode.Phi, merged);
            var carriedPhi = new Instruction(baseIndex + 31, OpCode.Phi, carried);
            var lookup = new Lookup
            {
                Head = new Instruction(baseIndex, OpCode.Move, klass, new MemoryOperand(receiver)),
                Fast = fast,
                SlowCall = new Instruction(baseIndex + 21, OpCode.Call, new Immediate(0x1234), slowResult, receiver, ifaceLocal, slotLocal),
                InvokePhi = invokePhi,
                CarriedPhi = carriedPhi,
                Merged = merged,
                FastEntry = fastEntry,
                SlowResult = slowResult,
                Klass = klass,
                Carried = carried,
                Target = target,
                Hidden = hidden,
            };
            lookup.Body =
            [
                lookup.Head,
                new(baseIndex + 1, OpCode.Move, ifaceLocal, iface),
                new(baseIndex + 2, OpCode.Move, condition, new MemoryOperand(klass, addend: 0x12E)),
                new(baseIndex + 3, OpCode.ConditionalJump, slowStart, condition),
                fast,
                new(baseIndex + 11, OpCode.ShiftLeft, scaled, slot == 0 ? offset : indexed, new Immediate(4)),
                new(baseIndex + 12, OpCode.Add, sum, klass, scaled),
                new(baseIndex + 13, OpCode.Add, fastEntry, sum, new Immediate(0x138)),
                new(baseIndex + 14, OpCode.Jump, invokePhi),
                slowStart,
                lookup.SlowCall,
                new(baseIndex + 22, OpCode.Jump, invokePhi),
                invokePhi,
                carriedPhi,
                new(baseIndex + 32, OpCode.CallVoid, new Immediate(0x5678), carried),
                new(baseIndex + 33, OpCode.Move, target, new MemoryOperand(merged)),
                new(baseIndex + 34, OpCode.Move, hidden, new MemoryOperand(merged, addend: 8)),
                new(baseIndex + 35, OpCode.Jump, join),
            ];
            if (slot != 0)
                lookup.Body.Insert(lookup.Body.IndexOf(fast) + 1, new(baseIndex + 15, OpCode.Add, indexed, offset, new Immediate(slot)));
            return lookup;
        }

        var first = Build("a", 100, disposable, dispose.Definition!.slot);
        var second = shape == "otherInterface"
            ? Build("b", 200, enumerator, moveNext.Definition!.slot)
            : Build("b", 200, disposable, dispose.Definition!.slot);
        var instructions = new List<Instruction> { new(0, OpCode.ConditionalJump, second.Head, pick) };
        instructions.AddRange(first.Body);
        instructions.AddRange(second.Body);
        instructions.AddRange([join, hiddenJoin, dispatch, new(93, OpCode.Return)]);

        var cfg = new ISILControlFlowGraph(instructions);
        cfg.RemoveUnreachableBlocks();
        cfg.MergeCallBlocks();
        foreach (var lookup in new[] { first, second })
        {
            var merge = cfg.Blocks.Single(b => b.Instructions.Contains(lookup.InvokePhi));
            var fastFirst = merge.Predecessors.Select(p => p.Instructions.Contains(lookup.Fast)).ToList();
            lookup.InvokePhi.SetOperands(new IOperand[] { lookup.Merged }.Concat(fastFirst.Select(f => f ? lookup.FastEntry : (IOperand)lookup.SlowResult)).ToList());
            // A value that only passes through the lookup, and one the lookup itself changes.
            var carriedTwoValues = shape == "carriedTwoValues" && lookup == first;
            lookup.CarriedPhi.SetOperands(new IOperand[] { lookup.Carried }.Concat(fastFirst.Select(f => carriedTwoValues && f ? lookup.FastEntry : (IOperand)receiver)).ToList());
        }
        var joinBlock = cfg.Blocks.Single(b => b.Instructions.Contains(join));
        var fromFirst = joinBlock.Predecessors.Select(p => p.Instructions.Contains(first.InvokePhi)).ToList();
        join.SetOperands(new IOperand[] { join.Operands[0] }.Concat(fromFirst.Select(f => (IOperand)(f ? first.Target : second.Target))).ToList());
        hiddenJoin.SetOperands(new IOperand[] { hiddenJoin.Operands[0] }.Concat(fromFirst.Select(f => (IOperand)(f ? first.Hidden : second.Hidden))).ToList());

        var caller = new InjectedMethodAnalysisContext(objectType, "Caller", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = cfg, Locals = locals, ParameterLocals = []
        };

        InterfaceDispatchRecovery.Run(caller)?.Invoke();

        Assert.That(dispatch.OpCode, Is.EqualTo(resolved ? OpCode.CallVoid : OpCode.IndirectCall));
        if (!resolved)
            return;
        Assert.That(dispatch.Operands[0], Is.SameAs(dispose));
        Assert.That(cfg.Instructions.Contains(second.SlowCall), Is.False);
        Assert.That(second.CarriedPhi.OpCode, Is.EqualTo(OpCode.Move), "one value along every path is copied from the head");
        Assert.That(second.CarriedPhi.Operands, Is.EqualTo(new IOperand[] { second.Carried, receiver }));
        // A phi merging a value the lookup computes stays, and so does its lookup.
        Assert.That(cfg.Instructions.Contains(first.SlowCall), Is.EqualTo(shape == "carriedTwoValues"));
    }
}
