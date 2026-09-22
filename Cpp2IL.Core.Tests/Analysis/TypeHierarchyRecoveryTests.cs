using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class TypeHierarchyRecoveryTests
{
    private ApplicationAnalysisContext _app = null!;
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
    }

    private (ISILControlFlowGraph Graph, List<LocalVariable> Locals, Instruction Guard, Instruction Check) Create(
        bool inverted = false, int scale = 3, bool wrongTarget = false, bool sideEffect = false, bool differentFailure = false,
        bool phi = false, bool mixedPhi = false, bool guardNot = false, bool extended = false)
    {
        var objectType = _app.SystemTypes.SystemObjectType;
        var type = new InjectedTypeAnalysisContext(objectType.DeclaringAssembly, "Tests", "Derived", objectType, TypeAttributes.Public);
        var locals = new List<LocalVariable>();
        LocalVariable Local(string name, TypeAnalysisContext? ty = null)
        {
            var local = new LocalVariable(name, new Register(null, name), ty);
            locals.Add(local);
            return local;
        }
        var receiver = Local("obj", objectType);
        var klass = Local("klass");
        var target = Local("target");
        var target2 = Local("target2");
        var objectDepth = Local("objectDepth");
        var targetDepth = Local("targetDepth");
        var hierarchy = Local("hierarchy");
        var scaled = Local("scaled");
        var address = Local("address");
        var entry = Local("entry");
        var condition = Local("condition", _app.SystemTypes.SystemBooleanType);
        var not = Local("not", _app.SystemTypes.SystemBooleanType);
        var match = Local("match", _app.SystemTypes.SystemBooleanType);
        var failure = new Instruction(90, OpCode.Return, new Immediate(0));
        var different = new Instruction(91, OpCode.Return, new Immediate(2));
        var success = new Instruction(92, OpCode.Return, new Immediate(1));
        var check = new Instruction(30, inverted ? OpCode.CheckNotEqual : OpCode.CheckEqual, match, entry, target);
        var guard = new Instruction(10, OpCode.ConditionalJump, differentFailure ? different : failure, guardNot ? not : condition);
        var loadHierarchy = new Instruction(20, OpCode.Move, hierarchy, new MemoryOperand(klass, addend: 0xC8));
        if (guardNot) guard.SetOperand(0, loadHierarchy);
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, klass, new MemoryOperand(receiver)),
            new(1, OpCode.Move, target2, mixedPhi ? objectType : type),
            new(2, OpCode.Move, target, type),
        };
        if (phi)
        {
            var merged = Local("mergedTarget");
            instructions.Add(new Instruction(3, OpCode.Phi, merged, target, target2));
            check.SetOperand(2, merged);
        }
        instructions.AddRange(new Instruction[]
        {
            new(4, OpCode.Move, objectDepth, new MemoryOperand(klass, addend: 0x130)),
            new(5, OpCode.Move, targetDepth, new MemoryOperand(wrongTarget ? klass : target, addend: 0x130)),
            new(6, OpCode.CheckLess, condition, objectDepth, targetDepth),
        });
        if (guardNot) instructions.Add(new Instruction(7, OpCode.Not, not, condition));
        instructions.Add(guard);
        if (guardNot) instructions.Add(new Instruction(11, OpCode.Jump, failure));
        instructions.Add(loadHierarchy);
        var shiftSource = targetDepth;
        if (extended)
        {
            shiftSource = Local("extendedDepth");
            instructions.Add(new Instruction(20, OpCode.ZeroExtend, shiftSource, targetDepth, new Immediate(32)));
        }
        instructions.AddRange(new Instruction[]
        {
            new(21, OpCode.ShiftLeft, scaled, shiftSource, new Immediate(scale)),
            new(22, OpCode.Add, address, hierarchy, scaled),
            new(23, OpCode.Move, entry, new MemoryOperand(address, addend: -8)),
        });
        if (sideEffect) instructions.Add(new Instruction(24, OpCode.CallVoid, new Immediate(1234)));
        instructions.Add(check);
        instructions.Add(new Instruction(31, OpCode.ConditionalJump, inverted ? failure : success, match));
        instructions.Add(new Instruction(32, OpCode.Jump, inverted ? success : failure));
        instructions.Add(failure);
        instructions.Add(different);
        instructions.Add(success);
        return (new ISILControlFlowGraph(instructions), locals, guard, check);
    }

    [TestCase(false)]
    [TestCase(true)]
    public void RecognizesUnsignedHierarchyDepth(bool wide)
    {
        var (graph, locals, _, check) = Create();
        var depth = graph.Instructions.Single(i => i.OpCode == OpCode.CheckLess);
        depth.AddOperands([wide ? _app.SystemTypes.SystemUInt64Type : _app.SystemTypes.SystemUInt32Type]);
        TypeHierarchyRecovery.Run(graph, locals, _app.SystemTypes.SystemBooleanType);
        Assert.That(check.OpCode, Is.EqualTo(OpCode.IsInstance));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void RecoversClassCheckAndKeepsPolarity(bool inverted)
    {
        var (graph, locals, _, check) = Create(inverted);
        TypeHierarchyRecovery.Run(graph, locals, _app.SystemTypes.SystemBooleanType);
        Assert.That(graph.Instructions.Count(i => i.OpCode == OpCode.IsInstance), Is.EqualTo(1));
        Assert.That(check.OpCode, Is.EqualTo(inverted ? OpCode.CheckEqual : OpCode.IsInstance));
        TypeHierarchyRecovery.Run(graph, locals, _app.SystemTypes.SystemBooleanType);
        Assert.That(graph.Instructions.Count(i => i.OpCode == OpCode.IsInstance), Is.EqualTo(1));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void RemovesGuardAndDeadNativeLoads(bool negatedGuard)
    {
        var (graph, locals, guard, _) = Create(guardNot: negatedGuard);
        TypeHierarchyRecovery.Run(graph, locals, _app.SystemTypes.SystemBooleanType);
        Assert.That(guard.Operands[1], Is.EqualTo(new Immediate(negatedGuard ? 1 : 0)));
        Assert.That(graph.Instructions.Any(i => i.Operands.Any(o => o is MemoryOperand)), Is.False);
    }

    [Test]
    public void RecoversZeroExtendedByteDepth()
    {
        var (graph, locals, guard, check) = Create(extended: true);
        TypeHierarchyRecovery.Run(graph, locals, _app.SystemTypes.SystemBooleanType);
        Assert.That(check.OpCode, Is.EqualTo(OpCode.IsInstance));
        Assert.That(guard.Operands[1], Is.EqualTo(new Immediate(0)));
    }

    [TestCase(0, false)]
    [TestCase(2, false)]
    [TestCase(3, true)]
    public void RejectsWrongScaleOrTarget(int scale, bool wrongTarget)
    {
        var (graph, locals, guard, check) = Create(scale: scale, wrongTarget: wrongTarget);
        TypeHierarchyRecovery.Run(graph, locals, _app.SystemTypes.SystemBooleanType);
        Assert.That(check.OpCode, Is.EqualTo(OpCode.CheckEqual));
        Assert.That(guard.Operands[1], Is.TypeOf<LocalVariable>());
    }

    [TestCase(false)]
    [TestCase(true)]
    public void ResolvesOnlyIdenticalMetadataPhiInputs(bool mixed)
    {
        var (graph, locals, _, check) = Create(phi: true, mixedPhi: mixed);
        TypeHierarchyRecovery.Run(graph, locals, _app.SystemTypes.SystemBooleanType);
        Assert.That(check.OpCode, Is.EqualTo(mixed ? OpCode.CheckEqual : OpCode.IsInstance));
    }

    [TestCase(true, false)]
    [TestCase(false, true)]
    public void RetainsGuardWithSideEffectsOrDifferentFailure(bool sideEffect, bool differentFailure)
    {
        var (graph, locals, guard, _) = Create(sideEffect: sideEffect, differentFailure: differentFailure);
        TypeHierarchyRecovery.Run(graph, locals, _app.SystemTypes.SystemBooleanType);
        Assert.That(guard.Operands[1], Is.TypeOf<LocalVariable>());
    }

    private (ISILControlFlowGraph Graph, List<LocalVariable> Locals, Instruction Guard) CreateResult(
        bool merge, bool inverted = false, bool wrongFallback = false, bool sideEffect = false,
        bool differingPhi = false, bool subtraction = false, bool failureSideEffect = false)
    {
        var (original, locals, guard, check) = Create(inverted: inverted, sideEffect: sideEffect);
        var failure = ((Block)guard.Operands[0]).Instructions[0];
        guard.SetOperand(0, failure);
        var instructions = original.Instructions.Where(i => i.Index <= check.Index).OrderBy(i => i.Index).ToList();
        LocalVariable Local(string name)
        {
            var local = new LocalVariable(name, new Register(null, name), _app.SystemTypes.SystemBooleanType);
            locals.Add(local);
            return local;
        }
        if (subtraction)
        {
            var difference = Local("difference");
            instructions.Insert(instructions.IndexOf(check), new Instruction(29, OpCode.Subtract,
                difference, check.Operands[1], check.Operands[2]));
            check.SetOperands(check.Operands[0], difference, new Immediate(0));
        }
        var copy = Local("resultCopy");
        instructions.Add(new Instruction(31, OpCode.Move, copy, check.Destination!));
        var miss = new Immediate((inverted ^ wrongFallback) ? 1 : 0);
        if (!merge)
        {
            instructions.Add(new Instruction(32, OpCode.Return, copy));
            failure.SetOperands(miss);
            if (failureSideEffect)
            {
                failure.OpCode = OpCode.CallVoid;
                failure.SetOperands(new Immediate(1234));
                instructions.Add(failure);
                instructions.Add(new Instruction(91, OpCode.Return, miss));
            }
            else instructions.Add(failure);
            return (new ISILControlFlowGraph(instructions), locals, guard);
        }
        var fallback = Local("fallback");
        var merged = Local("mergedResult");
        var phi = new Instruction(100, OpCode.Phi, merged, copy, fallback);
        instructions.Add(new Instruction(32, OpCode.Jump, phi));
        failure.OpCode = OpCode.Move;
        failure.SetOperands(fallback, miss);
        instructions.Add(failure);
        if (failureSideEffect) instructions.Add(new Instruction(91, OpCode.CallVoid, new Immediate(1234)));
        instructions.Add(new Instruction(92, OpCode.Jump, phi));
        instructions.Add(phi);
        Instruction? extraPhi = null;
        if (differingPhi)
        {
            extraPhi = new Instruction(101, OpCode.Phi, Local("otherResult"), new Immediate(7), new Immediate(8));
            instructions.Add(extraPhi);
        }
        instructions.Add(new Instruction(102, OpCode.Return, merged));
        var graph = new ISILControlFlowGraph(instructions);
        var mergeBlock = graph.Blocks.Single(b => b.Instructions.Contains(phi));
        phi.SetOperands(merged);
        foreach (var predecessor in mergeBlock.Predecessors)
            phi.AddOperands(new[] { predecessor.Instructions.Contains(check) ? copy : fallback });
        return (graph, locals, guard);
    }

    [TestCase(false, false, false)]
    [TestCase(false, true, false)]
    [TestCase(true, false, false)]
    [TestCase(true, true, false)]
    [TestCase(true, false, true)]
    public void RemovesResultGuardOnlyWhenMissValuesAgree(bool merge, bool inverted, bool subtraction)
    {
        var (graph, locals, guard) = CreateResult(merge, inverted, subtraction: subtraction);
        TypeHierarchyRecovery.Run(graph, locals, _app.SystemTypes.SystemBooleanType);
        Assert.That(guard.Operands[1], Is.EqualTo(new Immediate(0)));
        Assert.That(graph.Instructions.Any(i => i.Operands.Any(o => o is MemoryOperand)), Is.False);
        TypeHierarchyRecovery.Run(graph, locals, _app.SystemTypes.SystemBooleanType);
        Assert.That(graph.Instructions.Count(i => i.OpCode == OpCode.IsInstance), Is.EqualTo(1));
    }

    [TestCase(false, true, false, false, false)]
    [TestCase(true, true, false, false, false)]
    [TestCase(false, false, true, false, false)]
    [TestCase(true, false, true, false, false)]
    [TestCase(true, false, false, true, false)]
    [TestCase(false, false, false, false, true)]
    [TestCase(true, false, false, false, true)]
    public void RetainsResultGuardForObservableDifferences(bool merge, bool wrongFallback, bool sideEffect,
        bool differingPhi, bool failureSideEffect)
    {
        var (graph, locals, guard) = CreateResult(merge, wrongFallback: wrongFallback, sideEffect: sideEffect,
            differingPhi: differingPhi, failureSideEffect: failureSideEffect);
        TypeHierarchyRecovery.Run(graph, locals, _app.SystemTypes.SystemBooleanType);
        Assert.That(guard.Operands[1], Is.TypeOf<LocalVariable>());
    }

    [Test]
    public void IsInstanceTracksReceiverAsSource()
    {
        var (graph, locals, _, _) = Create();
        TypeHierarchyRecovery.Run(graph, locals, _app.SystemTypes.SystemBooleanType);
        var test = graph.Instructions.Single(i => i.OpCode == OpCode.IsInstance);
        Assert.That(test.Sources.ToArray(), Is.EqualTo(new[] { test.Operands[2] }));
        Assert.That(test.Destination, Is.SameAs(test.Operands[0]));
    }
}
