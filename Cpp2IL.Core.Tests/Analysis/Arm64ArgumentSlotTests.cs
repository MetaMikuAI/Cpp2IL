using System.Linq;
using System.Reflection;
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
    [TestCase("float", 1)]
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
            case "float": pair.Fields[0].FieldType = app.SystemTypes.SystemDoubleType; break;
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
}
