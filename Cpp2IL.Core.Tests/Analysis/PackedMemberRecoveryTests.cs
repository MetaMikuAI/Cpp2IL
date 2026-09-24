using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class PackedMemberRecoveryTests
{
    // An 8-byte sequential struct with 4-byte members at 0 and 4, integers preferred (e.g. Vector2Int).
    private static TypeAnalysisContext PackedPair(ApplicationAnalysisContext app) => app.AllTypes
        .Where(t => t is { Type: Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE, IsEnumType: false } && t.GenericParameters.Count == 0
            && (t.Attributes & TypeAttributes.ExplicitLayout) == 0 && TypeSizes.UnboxedSize(t, 8) == 8
            && t.Fields.Where(f => !f.IsStatic).Select(f => (f.Offset, f.FieldType.FullName)).ToList() is [(0, var low), (4, var high)]
            && low == high && low is "System.Int32" or "System.UInt32" or "System.Single")
        .OrderBy(t => t.Fields.First(f => !f.IsStatic).FieldType.FullName == "System.Int32" ? 0 : 1)
        .First();

    private static MethodAnalysisContext Method(ApplicationAnalysisContext app, params Instruction[] instructions) =>
        new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Packed", app.SystemTypes.SystemVoidType,
            MethodAttributes.Static | MethodAttributes.Public, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([.. instructions, new Instruction(instructions.Length, OpCode.Return)]),
            Locals = [], ParameterLocals = []
        };

    [TestCase(null)]
    [TestCase("System.Int64")]
    [TestCase("System.UInt64")]
    public void UpperHalfShiftReadsTheMemberAtOffsetFour(string? shiftType)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var packed = PackedPair(app);
        var integer = packed.Fields.First(f => !f.IsStatic).FieldType.FullName != "System.Single";
        var value = new LocalVariable("value", new Register(null, "value"), packed);
        var high = new LocalVariable("high", new Register(null, "high"));
        var shift = shiftType == null
            ? new Instruction(0, OpCode.ShiftRight, high, value, new Immediate(32))
            : new Instruction(0, OpCode.ShiftRight, high, value, new Immediate(32), app.AllTypes.Single(t => t.FullName == shiftType));
        var expected = shiftType == null || integer;

        Assert.That(LocalVariables.RecoverPackedMembers(Method(app, shift)), Is.EqualTo(expected));
        if (!expected)
            return;
        Assert.That(shift.OpCode, Is.EqualTo(shiftType switch
        {
            null => OpCode.Move, "System.Int64" => OpCode.SignExtend, _ => OpCode.ZeroExtend
        }));
        var read = (FieldReference)shift.Operands[1];
        Assert.That(read.Field.Offset, Is.EqualTo(4));
        Assert.That(read.Local, Is.SameAs(value));
        Assert.That(shift.Operands[0], Is.SameAs(high));
    }

    [Test]
    public void LowHalfMaskReadsTheMemberAtOffsetZeroZeroExtended()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var packed = PackedPair(app);
        var integer = packed.Fields.First(f => !f.IsStatic).FieldType.FullName != "System.Single";
        var value = new LocalVariable("value", new Register(null, "value"), packed);
        var low = new LocalVariable("low", new Register(null, "low"));
        var mask = new Instruction(0, OpCode.And, low, value, new Immediate(0xFFFFFFFF));

        Assert.That(LocalVariables.RecoverPackedMembers(Method(app, mask)), Is.EqualTo(integer));
        if (!integer)
            return;
        Assert.That(mask.OpCode, Is.EqualTo(OpCode.ZeroExtend));
        Assert.That(((FieldReference)mask.Operands[1]).Field.Offset, Is.EqualTo(0));
        Assert.That(mask.Operands[2], Is.EqualTo(new Immediate(32)));
    }

    [TestCase("narrowShift")]
    [TestCase("otherAmount")]
    [TestCase("otherMask")]
    [TestCase("wideStruct")]
    [TestCase("untyped")]
    [TestCase("reference")]
    [TestCase("thirtyTwoBit")]
    public void LeavesEverythingElseAlone(string shape)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        if (shape == "thirtyTwoBit")
            app.Binary.is32Bit = true;
        var type = shape switch
        {
            "wideStruct" => app.AllTypes.Single(t => t.FullName == "UnityEngine.Bounds"),
            "untyped" => null,
            "reference" => app.SystemTypes.SystemStringType,
            _ => PackedPair(app)
        };
        var value = new LocalVariable("value", new Register(null, "value"), type);
        var result = new LocalVariable("result", new Register(null, "result"));
        var instruction = shape switch
        {
            "narrowShift" => new Instruction(0, OpCode.ShiftRight, result, value, new Immediate(32), app.SystemTypes.SystemUInt32Type),
            "otherAmount" => new Instruction(0, OpCode.ShiftRight, result, value, new Immediate(16)),
            "otherMask" => new Instruction(0, OpCode.And, result, value, new Immediate(0xFFFF)),
            _ => new Instruction(0, OpCode.ShiftRight, result, value, new Immediate(32)),
        };
        var before = instruction.ToString();

        Assert.That(LocalVariables.RecoverPackedMembers(Method(app, instruction)), Is.False);
        Assert.That(instruction.ToString(), Is.EqualTo(before));
    }
}
