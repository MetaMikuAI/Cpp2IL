using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class AggregatePieceRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    [TestCase("System.Nullable`1", OpCode.And, 0xFF, "hasValue")]
    [TestCase("System.Nullable`1", OpCode.And, 0xFFFF, null)]
    [TestCase("System.Collections.Generic.KeyValuePair`2", OpCode.ShiftRight, 32, "value")]
    [TestCase("System.Collections.Generic.KeyValuePair`2", OpCode.ShiftRight, 16, null)]
    [TestCase("System.Collections.Generic.KeyValuePair`2", OpCode.And, 0xFFFFFFFF, "key")]
    public void RegisterHeldStruct_MaskedOrShifted_ReadsTheMember(string typeName, OpCode opCode, long amount, string? member)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var definition = app.AllTypes.Single(t => t.FullName == typeName);
        var argument = typeName.Contains("Nullable") ? app.SystemTypes.SystemBooleanType : app.SystemTypes.SystemInt32Type;
        var type = new GenericInstanceTypeAnalysisContext(definition, definition.GenericParameters.Select(_ => argument));
        var source = new LocalVariable("source", new Register(null, "source"), type);
        var bits = new LocalVariable("bits", new Register(null, "bits"), null);
        var piece = new Instruction(0, opCode, bits, source, new Immediate(amount));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
        {
            Locals = [source, bits], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph([piece, new Instruction(1, OpCode.Return, bits)]),
        };

        AggregatePieceRecovery.Run(method);

        if (member == null)
        {
            Assert.That(piece.OpCode, Is.EqualTo(opCode));
            return;
        }
        Assert.That(piece.OpCode, Is.EqualTo(OpCode.Move));
        var read = (FieldReference)piece.Operands[1];
        Assert.That((read.Field.Name, read.Local), Is.EqualTo((member, source)));
        Assert.That(bits.Type!.FullName, Is.EqualTo(argument.FullName));
    }
}
