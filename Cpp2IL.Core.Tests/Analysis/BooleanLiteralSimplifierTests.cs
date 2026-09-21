using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class BooleanLiteralSimplifierTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [TestCase(OpCode.And, 0, OpCode.Move, true)]
    [TestCase(OpCode.And, 1, OpCode.Move, false)]
    [TestCase(OpCode.Or, 0, OpCode.Move, false)]
    [TestCase(OpCode.Or, 1, OpCode.Move, true)]
    [TestCase(OpCode.Xor, 0, OpCode.Move, false)]
    [TestCase(OpCode.Xor, 1, OpCode.Not, false)]
    public void SimplifiesBothOperandOrdersAndPreservesTruthTable(OpCode opcode, int value, OpCode expected, bool constant)
    {
        foreach (var reversed in new[] { false, true })
        {
            var flag = Local("flag", "Boolean");
            var literal = new Immediate(value);
            var result = Local("result", "Boolean");
            var instruction = new Instruction(0, opcode, result,
                reversed ? literal : flag, reversed ? flag : literal);
            var method = Method(instruction);
            BooleanFlagSimplifier.SimplifyLiteralOperations(method);
            Assert.That(instruction.OpCode, Is.EqualTo(expected));
            if (constant)
                Assert.That(((Immediate)instruction.Operands[1]).Value, Is.EqualTo(value));
            else
                Assert.That(instruction.Operands[1], Is.SameAs(flag));
            foreach (var input in new[] { 0, 1 })
            {
                var before = opcode == OpCode.And ? input & value : opcode == OpCode.Or ? input | value : input ^ value;
                var after = constant ? value : expected == OpCode.Not ? 1 - input : input;
                Assert.That(after, Is.EqualTo(before));
            }
            BooleanFlagSimplifier.SimplifyLiteralOperations(method);
            Assert.That(instruction.OpCode, Is.EqualTo(expected));
            Assert.That(instruction.Operands.Count, Is.EqualTo(2));
        }
    }

    [TestCase("Boolean", "IntPtr", 1)]
    [TestCase("Boolean", "Int32", 1)]
    [TestCase("Int32", "Boolean", 1)]
    [TestCase(null, "Boolean", 1)]
    [TestCase("Boolean", null, 1)]
    [TestCase("Boolean", "Boolean", 2)]
    [TestCase("Boolean", "Boolean", -1)]
    public void LeavesUnprovenDomainsAndIntegerResultsUnchanged(string? input, string? output, long value)
    {
        var instruction = new Instruction(0, OpCode.Xor, Local("result", output), Local("flag", input), new Immediate(value));
        BooleanFlagSimplifier.SimplifyLiteralOperations(Method(instruction));
        Assert.That(instruction.OpCode, Is.EqualTo(OpCode.Xor));
        Assert.That(instruction.Operands.Count, Is.EqualTo(3));
    }

    private static LocalVariable Local(string name, string? type) => new(name, new Register(null, name),
        type == null ? null : Cpp2IlApi.CurrentAppContext!.AssembliesByName["mscorlib"].GetTypeByFullName("System." + type));

    private static MethodAnalysisContext Method(Instruction instruction)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        return new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "BooleanLiteral",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([instruction, new Instruction(1, OpCode.Return)]),
        };
    }
}
