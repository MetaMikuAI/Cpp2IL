using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Isil;

public class Arm64NumericConversionTests
{
    // Encodings cross-checked with llvm-mc -triple=aarch64 -show-encoding.
    [TestCase(0x1e380020u, "Single", "Int32", 0, 0)]
    [TestCase(0x9e790020u, "Double", "UInt64", 0, 0)]
    [TestCase(0x1e300020u, "Single", "Int32", 1, 0)]
    [TestCase(0x9e710020u, "Double", "UInt64", 1, 0)]
    [TestCase(0x1e280020u, "Single", "Int32", 2, 0)]
    [TestCase(0x9e690020u, "Double", "UInt64", 2, 0)]
    [TestCase(0x1e200020u, "Single", "Int32", 3, 0)]
    [TestCase(0x9e610020u, "Double", "UInt64", 3, 0)]
    [TestCase(0x1e240020u, "Single", "Int32", 4, 0)]
    [TestCase(0x9e650020u, "Double", "UInt64", 4, 0)]
    [TestCase(0x1e220020u, "Int32", "Single", 0, 0)]
    [TestCase(0x9e630020u, "UInt64", "Double", 0, 0)]
    [TestCase(0x1e624020u, "Double", "Single", 0, 0)]
    [TestCase(0x1e22c020u, "Single", "Double", 0, 0)]
    [TestCase(0x1e18e020u, "Single", "Int32", 0, 8)]
    [TestCase(0x1e02e020u, "Int32", "Single", 0, 8)]
    [TestCase(0x5e21d820u, "Int32", "Single", 0, 0)]
    [TestCase(0x5e21a820u, "Single", "Int32", 3, 0)]
    [TestCase(0x5e21c820u, "Single", "Int32", 4, 0)]
    [TestCase(0x7e61a820u, "Double", "UInt64", 3, 0)]
    [TestCase(0x7e61c820u, "Double", "UInt64", 4, 0)]
    public void ScalarConversionsPreserveBothTypesAndRounding(uint word, string source, string target, int rounding, int fractionalBits)
    {
        var operation = Lift(word);
        Assert.That(operation.OpCode, Is.EqualTo(OpCode.ConvertNumeric));
        var conversion = (NumericConversion)operation.Operands[2];
        Assert.That(conversion.SourceType.FullName, Is.EqualTo("System." + source));
        Assert.That(conversion.TargetType.FullName, Is.EqualTo("System." + target));
        Assert.That((int)conversion.Rounding, Is.EqualTo(rounding));
        Assert.That(conversion.FractionalBits, Is.EqualTo(fractionalBits));
        Assert.That(operation.SourcesAndConstants, Is.EqualTo(new[] { operation.Operands[1] }));
        Assert.That(operation.Destination, Is.EqualTo(operation.Operands[0]));
    }

    [Test]
    public void UnmodeledVectorConversionIsNotSilentlyCopied()
        => Assert.That(Lift(0x0ea1b820).OpCode, Is.EqualTo(OpCode.NotImplemented));

    [Test]
    public void HalfPrecisionIsNotGuessedAndZeroRegisterWritesAreDiscarded()
    {
        Assert.That(Lift(0x1ee24020).OpCode, Is.EqualTo(OpCode.NotImplemented));
        Assert.That(Lift(0x1e38003f).OpCode, Is.EqualTo(OpCode.Nop));
    }

    [Test]
    public void ConversionCannotPropagateFloatingTypeOrValueIntoIntegerIndex()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var source = new LocalVariable("value", new Register(null, "V0"), app.SystemTypes.SystemSingleType);
        var index = new LocalVariable("index", new Register(null, "X0"));
        var copy = new LocalVariable("copy", new Register(null, "X1"));
        var conversion = new Instruction(0, OpCode.ConvertNumeric, index, source,
            new NumericConversion(app.SystemTypes.SystemSingleType, app.SystemTypes.SystemInt32Type));
        var returned = new Instruction(2, OpCode.Return, copy);
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Convert", app.SystemTypes.SystemInt32Type,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            Locals = [source, index, copy], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph([conversion, new(1, OpCode.Move, copy, index), returned])
        };
        LocalVariables.ResolveTypesAndFields(method);
        SsaSimplifier.Run(method);
        Assert.That(source.Type, Is.SameAs(app.SystemTypes.SystemSingleType));
        Assert.That(index.Type, Is.SameAs(app.SystemTypes.SystemInt32Type));
        Assert.That(copy.Type, Is.SameAs(app.SystemTypes.SystemInt32Type));
        Assert.That(returned.Operands[0], Is.SameAs(index));
        Assert.That(conversion.OpCode, Is.EqualTo(OpCode.ConvertNumeric));
    }

    [Test]
    public void ConversionInterpretationDoesNotInventUpstreamFieldTypes()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var source = new LocalVariable("unknown", new Register(null, "V0"));
        var result = new LocalVariable("result", new Register(null, "X0"));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Convert", app.SystemTypes.SystemInt32Type,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            Locals = [source, result], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph([
                new(0, OpCode.ConvertNumeric, result, source, new NumericConversion(app.SystemTypes.SystemSingleType, app.SystemTypes.SystemInt32Type)),
                new(1, OpCode.Return, result)])
        };
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(result.Type, Is.SameAs(app.SystemTypes.SystemInt32Type));
        Assert.That(source.Type, Is.Null);
    }

    private static Instruction Lift(uint word)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, []) { RawBytes = new BinarySlice(BitConverter.GetBytes(word)) };
        foreach (var name in new[] { "adrpOffsets", "integerConstants" })
            typeof(NewArmV8InstructionSet).GetField(name, BindingFlags.Static | BindingFlags.NonPublic)!
                .SetValue(null, new Dictionary<string, ulong>());
        var decoded = Disassembler.Disassemble(BitConverter.GetBytes(word), 0, new Disassembler.Options(true, true, false)).Single();
        var instructions = new List<Instruction>();
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement", BindingFlags.Instance | BindingFlags.NonPublic)!
            .Invoke(new NewArmV8InstructionSet(), new object[] { decoded, instructions, new List<ulong>(), method, new HashSet<string>() });
        return instructions.Single();
    }
}
