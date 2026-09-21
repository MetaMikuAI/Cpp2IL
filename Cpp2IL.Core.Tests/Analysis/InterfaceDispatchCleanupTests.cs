using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterfaceDispatchCleanupTests
{
    [TestCase("stale", true)]
    [TestCase("classInit", true)]
    [TestCase("live", false)]
    [TestCase("unresolved", false)]
    [TestCase("sideEffect", false)]
    [TestCase("fieldRead", false)]
    [TestCase("fieldStore", false)]
    [TestCase("arrayIndex", false)]
    [TestCase("arrayBase", false)]
    [TestCase("arrayLength", false)]
    [TestCase("elementAddress", false)]
    [TestCase("address", false)]
    public void ResolvesDownstreamVirtualCallsBeforeCheckingLookupLiveness(string use, bool removed)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        app.InstructionSet = new NewArmV8InstructionSet();
        var objectType = app.SystemTypes.SystemObjectType;
        var disposable = app.AllTypes.Single(t => t.FullName == "System.IDisposable");
        var dispose = disposable.Methods.Single(m => m.Name == "Dispose");
        var virtualMethod = objectType.Methods.Single(m => m.Name == (use == "live" ? "Equals" : "ToString") && !m.IsStatic);
        var locals = new List<LocalVariable>();
        LocalVariable Local(string name, TypeAnalysisContext? type = null)
        {
            var local = new LocalVariable(name, new Register(null, name), type);
            locals.Add(local);
            return local;
        }
        var receiver = Local("receiver", objectType);
        var klass = Local("klass"); // Only type propagation can resolve the later virtual call.
        var iface = Local("iface");
        var condition = Local("condition", app.SystemTypes.SystemBooleanType);
        var offset = Local("offset");
        var scaled = Local("scaled");
        var sum = Local("sum");
        var fast = Local("fast");
        var slot = Local("slot");
        var slow = Local("slow");
        var merged = Local("merged");
        var stale = Local("stale");
        var target = Local("target");
        var result = Local("result");
        var virtualResult = Local("virtualResult");
        var fastStart = new Instruction(10, OpCode.Move, offset, new MemoryOperand(klass, addend: 0xB0));
        var slowStart = new Instruction(20, OpCode.Move, slot, new Immediate(dispose.Definition!.slot));
        var invokePhi = new Instruction(30, OpCode.Phi, merged, fast, slow);
        var stalePhi = new Instruction(31, OpCode.Phi, stale, offset, slot);
        var slowCall = new Instruction(21, OpCode.Call, new Immediate(0x1234), slow, receiver, iface, slot);
        var dispatch = new Instruction(33, OpCode.IndirectCall, target, result, receiver);
        var virtualCall = new Instruction(34, OpCode.IndirectCall,
            new MemoryOperand(klass, addend: use == "unresolved" ? 1 : 0x138 + virtualMethod.Definition!.slot * 16),
            virtualResult, receiver, stale);
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, klass, new MemoryOperand(receiver)),
            new(1, OpCode.Move, iface, disposable),
            new(2, OpCode.Move, condition, new MemoryOperand(klass, addend: 0x12E)),
            new(3, OpCode.ConditionalJump, slowStart, condition),
            fastStart,
            new(11, OpCode.ShiftLeft, scaled, offset, new Immediate(4)),
            new(12, OpCode.Add, sum, klass, scaled),
            new(13, OpCode.Add, fast, sum, new Immediate(0x138)),
            new(14, OpCode.Jump, invokePhi),
            slowStart,
            slowCall,
        };
        if (use == "sideEffect") instructions.Add(new(22, OpCode.CallVoid, new Immediate(0x5678)));
        instructions.AddRange([
            new(23, OpCode.Jump, invokePhi),
            invokePhi, stalePhi,
            new(32, OpCode.Move, target, new MemoryOperand(merged)),
            dispatch,
        ]);
        if (use == "classInit")
        {
            var flag = Local("initFlag");
            var masked = Local("initMasked");
            var pending = Local("initPending", app.SystemTypes.SystemBooleanType);
            var initialized = Local("initialized");
            var init = new Instruction(40, OpCode.Call, new Immediate(0x9876), initialized, klass, stale);
            instructions.AddRange([
                new(36, OpCode.Move, flag, new MemoryOperand(klass, addend: 0x135)),
                new(37, OpCode.And, masked, flag, new Immediate(1)),
                new(38, OpCode.CheckNotEqual, pending, masked, new Immediate(0)),
                new(39, OpCode.ConditionalJump, virtualCall, pending),
                init, new(41, OpCode.Jump, virtualCall),
            ]);
        }
        instructions.Add(virtualCall);
        var field = new InjectedFieldAnalysisContext("Value", app.SystemTypes.SystemInt32Type, FieldAttributes.Public, objectType);
        IOperand? liveOperand = use switch
        {
            "fieldRead" or "fieldStore" => new FieldReference(field, stale, 0x10),
            "arrayIndex" => new ArrayAccess(receiver, stale),
            "arrayBase" => new ArrayAccess(stale, new Immediate(0)),
            "arrayLength" => new ArrayLength(stale),
            "elementAddress" => new AddressOf(new ArrayAccess(receiver, stale)),
            "address" => new AddressOf(stale),
            _ => null,
        };
        if (liveOperand != null)
            instructions.Add(use == "fieldStore"
                ? new(35, OpCode.Move, liveOperand, new Immediate(1))
                : new(35, OpCode.CallVoid, new Immediate(0x5678), liveOperand));
        instructions.Add(new(36, OpCode.Return));
        var cfg = new ISILControlFlowGraph(instructions);
        cfg.RemoveUnreachableBlocks();
        cfg.MergeCallBlocks();
        var merge = cfg.Blocks.Single(b => b.Instructions.Contains(invokePhi));
        invokePhi.SetOperands(new IOperand[] { merged }.Concat(merge.Predecessors.Select(b => b.Instructions.Contains(fastStart) ? fast : slow)).ToList());
        stalePhi.SetOperands(new IOperand[] { stale }.Concat(merge.Predecessors.Select(b => b.Instructions.Contains(fastStart) ? offset : slot)).ToList());
        var caller = new InjectedMethodAnalysisContext(objectType, "Caller", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = cfg, Locals = locals, ParameterLocals = []
        };

        var retryCleanup = InterfaceDispatchRecovery.Run(caller);
        // The first pass must retain values still referenced by an unresolved call.
        Assert.That(cfg.Instructions.Contains(slowCall), Is.True);
        LocalVariables.ResolveTypesAndFields(caller);
        retryCleanup?.Invoke();
        if (use == "classInit")
        {
            Assert.That(cfg.Instructions.Contains(slowCall), Is.True,
                "The initializer still holds a guessed argument from the interface lookup");
            MetadataInitGuardRemover.RunSsaClassGuards(cfg, 0x135);
            retryCleanup?.Invoke();
        }

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.CallVoid));
        Assert.That(dispatch.Operands[0], Is.SameAs(dispose));
        Assert.That(virtualCall.OpCode, Is.EqualTo(use == "unresolved" ? OpCode.IndirectCall : OpCode.Call));
        Assert.That(cfg.Instructions.Contains(slowCall), Is.EqualTo(!removed));
        if (removed)
        {
            Assert.That(stalePhi.OpCode, Is.EqualTo(OpCode.Nop));
            Assert.That(virtualCall.Operands, Is.EqualTo(new IOperand[] { virtualMethod, virtualResult, receiver }));
        }
        else if (use is "live" or "unresolved")
            Assert.That(virtualCall.Operands, Does.Contain(stale));

        retryCleanup?.Invoke();
        Assert.That(cfg.Instructions.Contains(slowCall), Is.EqualTo(!removed));
    }
}
