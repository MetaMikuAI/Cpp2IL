using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Analysis;

public class Arm64ArgumentSlotTests
{
    private ApplicationAnalysisContext app = null!;
    private TypeAnalysisContext pair = null!;
    private readonly Arm64CallingConventionResolver convention = new();

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        app = TestGameLoader.LoadSimple2019Game();
        pair = app.AllTypes.Single(t => t.FullName == "System.Decimal");
        pair.Attributes = (pair.Attributes & ~TypeAttributes.LayoutMask) | TypeAttributes.SequentialLayout;
        pair.Definition!.Bitfield = (pair.Definition.Bitfield & ~(0xFu << 6)) | (1u << 11);
        pair.Fields.Clear();
        pair.Fields.Add(new InjectedFieldAnalysisContext("source", app.SystemTypes.SystemObjectType, FieldAttributes.Public, pair, 0));
        pair.Fields.Add(new InjectedFieldAnalysisContext("token", app.SystemTypes.SystemInt16Type, FieldAttributes.Public, pair, 8));
    }

    [TestCase("pair", 2)]
    [TestCase("fourInts", 2)]
    [TestCase("mixedFloat", 2)]
    [TestCase("hfa", 1)]
    [TestCase("offset", 1)]
    [TestCase("packed", 1)]
    [TestCase("explicit", 1)]
    [TestCase("empty", 1)]
    [TestCase("32bit", 1)]
    public void CountsOnlyProvenIntegerCompositeLayouts(string kind, int slots)
    {
        switch (kind)
        {
            case "fourInts":
                pair.Fields.Clear();
                for (var i = 0; i < 4; i++) pair.Fields.Add(new InjectedFieldAnalysisContext($"f{i}", app.SystemTypes.SystemInt32Type, FieldAttributes.Public, pair, i * 4));
                break;
            // A composite that is not homogeneous floating point still travels in X registers.
            case "mixedFloat": pair.Fields[0].FieldType = app.SystemTypes.SystemDoubleType; break;
            case "hfa":
                pair.Fields[0].FieldType = app.SystemTypes.SystemDoubleType;
                pair.Fields[1].FieldType = app.SystemTypes.SystemDoubleType;
                break;
            case "offset": pair.Fields[1].Offset = 10; break;
            case "packed": pair.Definition!.Bitfield |= 1u << 6; break;
            case "explicit": pair.Attributes = TypeAttributes.Public | TypeAttributes.ExplicitLayout; break;
            case "empty": pair.Fields.Clear(); break;
            case "32bit": app.Binary.is32Bit = true; break;
        }
        Assert.That(Arm64CallingConventionResolver.IntegerArgumentSlots(pair), Is.EqualTo(slots));
    }

    private InjectedMethodAnalysisContext Method(bool instance, params TypeAnalysisContext[] parameters) =>
        new(app.SystemTypes.SystemObjectType, "Consume", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | (instance ? 0 : MethodAttributes.Static), parameters);

    [TestCase(false)]
    [TestCase(true)]
    public void ManagedAndRawCallsAgreeAfterAnAggregate(bool instance)
    {
        var target = Method(instance, pair, app.SystemTypes.SystemSingleType, app.SystemTypes.SystemInt32Type);
        var start = instance ? 1 : 0;
        var expected = (instance ? new[] { "X0" } : new string[0])
            .Concat(new[] { $"X{start}", "V0", $"X{start + 2}", $"X{start + 3}" }).ToArray();
        Assert.That(convention.ResolveForManaged(target).Cast<Register>().Select(r => r.Name), Is.EqualTo(expected));
        var raw = convention.ResolveForUnmanaged(app, 0);
        var call = new Instruction(0, OpCode.Call, new Immediate(0), new Register(null, "X0"));
        call.AddOperands(raw);
        convention.RemapRawArguments(call, target);
        Assert.That(call.Operands.Skip(2).Cast<Register>().Select(r => r.Name), Is.EqualTo(expected));
        Assert.That(call.Operands.Skip(2).All(o => raw.Contains(o)), Is.True);
    }

    [TestCase(6, false)]
    [TestCase(7, true)]
    public void SpillsTheWholeCompositeWhenTwoRegistersAreUnavailable(int preceding, bool spills)
    {
        var target = Method(false, Enumerable.Repeat(app.SystemTypes.SystemInt32Type, preceding)
            .Concat(new[] { pair, app.SystemTypes.SystemInt32Type }).ToArray());
        var args = convention.ResolveForManaged(target);
        if (spills)
        {
            Assert.That(args[preceding], Is.TypeOf<StackOffset>());
            Assert.That(((StackOffset)args[preceding]).Offset, Is.Zero);
        }
        else Assert.That(((Register)args[preceding]).Name, Is.EqualTo("X6"));
        Assert.That(((StackOffset)args[preceding + 1]).Offset, Is.EqualTo(spills ? 16 : 0));
        Assert.That(((StackOffset)args[preceding + 2]).Offset, Is.EqualTo(spills ? 24 : 8));
    }
    [TestCase(2)]
    [TestCase(3)]
    [TestCase(4)]
    public void FloatingAggregateReservesAllComponents(int count)
    {
        // Use the matching real metadata size rather than Decimal's fixed 16 bytes.
        pair = app.AllTypes.Single(t => t.FullName == $"UnityEngine.Vector{count}");
        pair.Fields.Clear();
        for (var i = 0; i < count; i++)
            pair.Fields.Add(new InjectedFieldAnalysisContext($"f{i}", app.SystemTypes.SystemSingleType, FieldAttributes.Public, pair, i * 4));
        Assert.That(Arm64CallingConventionResolver.FloatingAggregateFields(pair), Has.Length.EqualTo(count));
        var target = Method(true, pair, app.SystemTypes.SystemSingleType, app.SystemTypes.SystemInt32Type);
        Assert.That(convention.ResolveForManaged(target).Cast<Register>().Select(r => r.Name),
            Is.EqualTo(new[] { "X0", "V0", $"V{count}", "X1", "X2" }));
        Assert.That(Arm64CallingConventionResolver.FloatingAggregateFields(app.SystemTypes.SystemSingleType), Is.Null);
        pair.Fields[1].Offset++;
        Assert.That(Arm64CallingConventionResolver.FloatingAggregateFields(pair), Is.Null);
    }

    [Test]
    public void FloatingAggregateBoundaryUnpacksParametersAndPacksBranchTargetReturns()
    {
        pair.Fields.Clear();
        for (var i = 0; i < 4; i++)
            pair.Fields.Add(new InjectedFieldAnalysisContext($"f{i}", app.SystemTypes.SystemSingleType, FieldAttributes.Public, pair, i * 4));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Identity", pair,
            MethodAttributes.Public | MethodAttributes.Static, [pair]);
        var ret = new Instruction(1, OpCode.Return, new Register(null, "X0"));
        var jump = new Instruction(0, OpCode.Jump, ret);
        var instructions = new System.Collections.Generic.List<Instruction> { jump, ret };
        InstructionSets.NewArmV8InstructionSet.RecoverFloatingAggregateBoundary(method, instructions);
        Assert.That(instructions, Has.Count.EqualTo(10));
        Assert.That(instructions.Take(4).All(i => i.Operands[1] is MemoryOperand), Is.True);
        Assert.That(jump.Operands[0], Is.SameAs(ret));
        Assert.That(ret.OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(instructions[^1].OpCode, Is.EqualTo(OpCode.Return));
        Assert.That(method.StackAggregates, Has.Count.EqualTo(1));
    }
    [Test]
    public void HiddenReturnUsesIncomingBufferEvenWhenX8IsClobbered()
    {
        var type = app.AllTypes.Single(t => t.FullName == "UnityEngine.Bounds");
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Get", type,
            MethodAttributes.Public, []);
        var ret = new Instruction(2, OpCode.Return, new Register(null, "X0"));
        var instructions = new System.Collections.Generic.List<Instruction>
        {
            new(0, OpCode.Move, new Register(null, "X19"), new Register(null, "X8")),
            new(1, OpCode.Move, new Register(null, "X8"), new Immediate(123)), ret
        };
        InstructionSets.NewArmV8InstructionSet.RecoverFloatingAggregateBoundary(method, instructions);
        Assert.That(instructions[0].OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(((Register)instructions[0].Operands[1]).Name, Is.EqualTo("X8"));
        Assert.That(ret.Operands[0], Is.EqualTo(instructions[0].Operands[0]));
        Assert.That(((Register)ret.Operands[0]).Name, Is.Not.EqualTo("X8"));
    }
    [Test]
    public void DoesNotRedirectGenericCompositeReturnFromUnprovenSize()
    {
        // The stripped fixture has no ValueTuple; model a generic composite whose
        // metadata size would otherwise trigger the hidden-buffer convention.
        var definition = app.AllTypes.Single(t => t.FullName == "UnityEngine.Bounds");
        var parameter = new GenericParameterTypeAnalysisContext("T", 0,
            LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            GenericParameterAttributes.None, definition);
        definition.GenericParameters.Add(parameter);
        var type = definition.MakeGenericInstanceType([app.SystemTypes.SystemInt32Type]);
        Assert.That(convention.ReturnsViaHiddenBuffer(new InjectedMethodAnalysisContext(
            app.SystemTypes.SystemObjectType, "Probe", type, MethodAttributes.Public, [])), Is.True);
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Get", type,
            MethodAttributes.Public, []);
        var ret = new Instruction(0, OpCode.Return, new Register(null, "X0"));
        var instructions = new System.Collections.Generic.List<Instruction> { ret };
        InstructionSets.NewArmV8InstructionSet.RecoverFloatingAggregateBoundary(method, instructions);
        Assert.That(instructions, Has.Count.EqualTo(1));
        Assert.That(((Register)ret.Operands[0]).Name, Is.EqualTo("X0"));
    }

    [Test]
    public void NestedCompositeCarriesOneMemberPerRegister()
    {
        var inner = app.AllTypes.Single(t => t.FullName == "UnityEngine.Vector4");
        inner.Definition!.Bitfield = (inner.Definition.Bitfield & ~(0xFu << 6)) | (1u << 11);
        inner.Fields.Clear();
        inner.Fields.Add(new InjectedFieldAnalysisContext("handle", app.SystemTypes.SystemIntPtrType, FieldAttributes.Public, inner, 0));
        inner.Fields.Add(new InjectedFieldAnalysisContext("version", app.SystemTypes.SystemUInt32Type, FieldAttributes.Public, inner, 8));
        pair.Fields.Clear();
        pair.Fields.Add(new InjectedFieldAnalysisContext("inner", inner, FieldAttributes.Public, pair, 0));
        Assert.That(Arm64CallingConventionResolver.IntegerArgumentSlots(pair), Is.EqualTo(2));
        Assert.That(Arm64CallingConventionResolver.IntegerCompositeMembers(pair), Is.EqualTo(new[] { (0L, 8), (8L, 4) }));
        inner.Fields[1].Offset = 12;
        Assert.That(Arm64CallingConventionResolver.IntegerArgumentSlots(pair), Is.EqualTo(1));
    }

    [Test]
    public void CompositeBoundaryUnpacksParameters()
    {
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Identity", pair,
            MethodAttributes.Public, [pair]);
        var operands = new NewArmV8InstructionSet().GetParameterOperandsFromMethod(method);
        Assert.That(operands.Cast<Register>().Select(r => r.Name),
            Is.EqualTo(new[] { "X0", "composite_parameter_0", "X3" }));
        var ret = new Instruction(0, OpCode.Return, new Register(null, "X0"));
        var instructions = new System.Collections.Generic.List<Instruction> { ret };
        NewArmV8InstructionSet.RecoverFloatingAggregateBoundary(method, instructions);
        Assert.That(instructions, Has.Count.EqualTo(3));
        // X1 and X2 carry the parameter's members; its padding is not read.
        Assert.That(instructions.Take(2).Select(i => (((Register)i.Operands[0]).Name, ((MemoryOperand)i.Operands[1]).Addend,
            ((MemoryOperand)i.Operands[1]).AccessSize)), Is.EqualTo(new[] { ("X1", 0L, 8), ("X2", 8L, 2) }));
        Assert.That(instructions[^1], Is.SameAs(ret));
    }

    [Test]
    public void CallClobbersCallerSavedRegistersButKeepsItsResult()
    {
        Register Reg(string name) => new(null, name);
        var argument = new Instruction(0, OpCode.Move, Reg("X1"), new Immediate(5));
        var saved = new Instruction(1, OpCode.Move, Reg("X19"), new Immediate(6));
        var call = new Instruction(2, OpCode.Call, new Immediate(0x1000), Reg("X0"), Reg("X1"));
        NewArmV8InstructionSet.ClobberCallerSaved(call);
        Assert.That(call.CallClobbers!.Select(r => r.Name), Does.Contain("X1").And.Contain("V31").And.Not.Contain("X0")
            .And.Not.Contain("X19").And.Not.Contain("V8"));
        var unknown = new Instruction(0, OpCode.Call, new Immediate(0x1000), Reg("X0"));
        NewArmV8InstructionSet.ClobberCallerSaved(unknown, unknownSignature: true);
        Assert.That(unknown.CallClobbers!.Select(r => r.Name), Does.Contain("X2").And.Contain("V4").And.Not.Contain("X1")
            .And.Not.Contain("V0").And.Not.Contain("V3"));
        var use = new Instruction(3, OpCode.Add, Reg("X2"), Reg("X1"), Reg("X19"));
        var ret = new Instruction(4, OpCode.Return, Reg("X0"));
        var graph = new ISILControlFlowGraph([argument, saved, call, use, ret]);
        SsaForm.Build(graph, new DominatorInfo(graph));
        Assert.That(call.Operands[2], Is.EqualTo(argument.Destination));
        Assert.That(use.Operands[1], Is.Not.EqualTo(argument.Destination));
        Assert.That(use.Operands[2], Is.EqualTo(saved.Destination));
        Assert.That(ret.Operands[0], Is.EqualTo(call.Destination));
        Assert.That(call.CallClobbers, Is.Null);
    }

    [Test]
    public void UnsetDeclaredArgumentKeepsItsValueButUnsetMethodInfoDoesNot()
    {
        // The callee never reads an argument the caller left unset since a call, e.g. an unused 'this'.
        Register Reg(string name) => new(null, name);
        var receiver = new Instruction(0, OpCode.Move, Reg("X0"), new Immediate(5));
        var methodInfo = new Instruction(1, OpCode.Move, Reg("X1"), new Immediate(6));
        var first = new Instruction(2, OpCode.CallVoid, new Immediate(0x1000), Reg("X0"), Reg("X1"));
        NewArmV8InstructionSet.ClobberCallerSaved(first);
        var second = new Instruction(3, OpCode.CallVoid, new Immediate(0x2000), Reg("X0"), Reg("X1")) { DeclaredArguments = 1 };
        var graph = new ISILControlFlowGraph([receiver, methodInfo, first, second, new(4, OpCode.Return)]);
        SsaForm.Build(graph, new DominatorInfo(graph));
        Assert.That(second.Operands[1], Is.EqualTo(receiver.Destination));
        Assert.That(second.Operands[2], Is.Not.EqualTo(methodInfo.Destination));
    }

    [Test]
    public void MergeThroughACallKeepsThePriorValue()
    {
        // A throw helper the graph still falls through must not leave a merge without a value.
        Register Reg(string name) => new(null, name);
        var value = new Instruction(0, OpCode.Move, Reg("X1"), new Immediate(5));
        var merge = new Instruction(4, OpCode.Move, Reg("X1"), Reg("X1"));
        var redefined = new Instruction(3, OpCode.Move, Reg("X1"), new Immediate(6));
        var call = new Instruction(2, OpCode.CallVoid, new Immediate(0x1000));
        NewArmV8InstructionSet.ClobberCallerSaved(call);
        var branch = new Instruction(1, OpCode.ConditionalJump, redefined, Reg("condition"));
        var join = new Instruction(5, OpCode.Return, Reg("X1"));
        var graph = new ISILControlFlowGraph([value, branch, call, new(6, OpCode.Jump, merge), redefined, merge, join]);
        SsaForm.Build(graph, new DominatorInfo(graph));
        var phi = graph.Instructions.Single(i => i.OpCode == OpCode.Phi);
        Assert.That(phi.Operands.Skip(1), Does.Contain(value.Destination).And.Contain(redefined.Destination));
    }

    private (MethodAnalysisContext Method, LocalVariable Receiver, long Offset) CompositeOwner(params LocalVariable[] locals)
    {
        var owner = app.AllTypes.Single(t => t.FullName == "UnityEngine.Object");
        var field = owner.Fields.Single(f => f.Name == "m_CachedPtr");
        field.FieldType = pair;
        var receiver = new LocalVariable("this", new Register(null, "X0"), owner) { IsThis = true };
        var method = new InjectedMethodAnalysisContext(owner, "Copy", app.SystemTypes.SystemVoidType, MethodAttributes.Public, [pair])
        {
            Locals = [receiver, .. locals]
        };
        return (method, receiver, field.Offset);
    }

    [Test]
    public void StoringBothRegistersOfACompositeParameterAssignsTheValue()
    {
        var value = new LocalVariable("value", new Register(null, "composite_parameter_0"), pair);
        var low = new LocalVariable("low", new Register(null, "X1"));
        var high = new LocalVariable("high", new Register(null, "X2"));
        var (method, receiver, offset) = CompositeOwner(value, low, high);
        method.ParameterLocals = [receiver, value];
        var lowStore = new Instruction(3, OpCode.Move, new MemoryOperand(receiver, addend: offset, accessSize: 8), low);
        var highStore = new Instruction(4, OpCode.Move, new MemoryOperand(receiver, addend: offset + 8, accessSize: 8), high);
        method.ControlFlowGraph = new ISILControlFlowGraph(
        [
            new(0, OpCode.Move, low, new MemoryOperand(value, addend: 0, accessSize: 8)),
            new(1, OpCode.Move, high, new MemoryOperand(value, addend: 8, accessSize: 2)),
            new(2, OpCode.Move, new LocalVariable("unrelated", new Register(null, "X9")), new Immediate(1)),
            lowStore, highStore, new(5, OpCode.Return)
        ]);
        Assert.That(AggregateCopyRecovery.Run(method), Is.True);
        Assert.That(lowStore.Operands[0], Is.TypeOf<FieldReference>());
        Assert.That(((FieldReference)lowStore.Operands[0]).Field.FieldType, Is.EqualTo(pair));
        Assert.That(lowStore.Operands[1], Is.SameAs(value));
        Assert.That(highStore.OpCode, Is.EqualTo(OpCode.Nop));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void PassingBothHalvesOfAFieldPassesTheField(bool callBetween)
    {
        var argument = new LocalVariable("argument", new Register(null, "composite_arg_10_0"), pair);
        var low = new LocalVariable("low", new Register(null, "X1"));
        var high = new LocalVariable("high", new Register(null, "X2"));
        var (method, receiver, offset) = CompositeOwner(argument, low, high);
        method.ParameterLocals = [receiver];
        var lowStore = new Instruction(3, OpCode.Move, new MemoryOperand(argument, addend: 0, accessSize: 8), low);
        var highStore = new Instruction(4, OpCode.Move, new MemoryOperand(argument, addend: 8, accessSize: 2), high);
        method.ControlFlowGraph = new ISILControlFlowGraph(
        [
            new(0, OpCode.Move, low, new MemoryOperand(receiver, addend: offset, accessSize: 8)),
            new(1, OpCode.Move, high, new MemoryOperand(receiver, addend: offset + 8, accessSize: 8)),
            callBetween ? new(2, OpCode.CallVoid, new Immediate(0x2000), receiver) : new(2, OpCode.Nop),
            lowStore, highStore, new(5, OpCode.CallVoid, new Immediate(0x1000), argument), new(6, OpCode.Return)
        ]);
        Assert.That(AggregateCopyRecovery.Run(method), Is.EqualTo(!callBetween));
        if (callBetween)
        {
            Assert.That(highStore.OpCode, Is.EqualTo(OpCode.Move));
            return;
        }
        Assert.That(lowStore.Operands[0], Is.SameAs(argument));
        Assert.That(((FieldReference)lowStore.Operands[1]).Local, Is.SameAs(receiver));
        Assert.That(highStore.OpCode, Is.EqualTo(OpCode.Nop));
    }
}
