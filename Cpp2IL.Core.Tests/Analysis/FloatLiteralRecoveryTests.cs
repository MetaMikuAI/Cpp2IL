using System.Collections.Generic;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class FloatLiteralRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [Test]
    public void RecoversBitPatternUsedByFloatArithmetic()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var single = app.SystemTypes.SystemSingleType;
        var method = new InjectedMethodAnalysisContext(single, "Test", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        var value = new LocalVariable("value", new Register(null, "value"), single);
        var result = new LocalVariable("result", new Register(null, "result"), single);
        var add = new Instruction(0, OpCode.Add, result, value, Imm(0x42000000));

        method.ControlFlowGraph = new ISILControlFlowGraph(new List<Instruction>
        {
            add,
            new(1, OpCode.Return)
        });

        FloatLiteralRecovery.Run(method);

        Assert.That(add.Operands[2], Is.EqualTo(new FloatLiteral(32f)));
    }
}
