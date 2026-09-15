using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class IntegerRecurrenceTests
{
    [TestCase("int", 0L, true)]
    [TestCase("long", 2147483648L, true)]
    [TestCase("int", 2147483648L, false)]
    [TestCase("pointer", 0L, false)]
    [TestCase("unknown", 0L, false)]
    [TestCase("nonrecurring", 0L, false)]
    [TestCase("conflict", 0L, false)]
    public void TypesOnlyClosedRecurrencesWithRepresentableSeeds(string kind, long seed, bool expected)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var type = kind switch
        {
            "long" => app.SystemTypes.SystemInt64Type,
            "pointer" => app.SystemTypes.SystemIntPtrType,
            "unknown" => null,
            _ => app.SystemTypes.SystemInt32Type
        };
        var sum = new LocalVariable("sum", new Register(null, "sum"));
        var next = new LocalVariable("next", new Register(null, "next"), kind == "conflict" ? app.SystemTypes.SystemInt64Type : null);
        var step = new LocalVariable("step", new Register(null, "step"), type);
        var unknown = new LocalVariable("other", new Register(null, "other"));
        var phi = new Instruction(0, OpCode.Phi, sum, new Immediate(seed), next);
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Sum", app.SystemTypes.SystemVoidType,
            MethodAttributes.Static | MethodAttributes.Public, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([phi,
                new(1, OpCode.Add, next, step, kind == "nonrecurring" ? unknown : sum), new(2, OpCode.Jump, phi)]),
            Locals = [sum, next, step, unknown], ParameterLocals = []
        };
        Assert.That(LocalVariables.PropagateIntegerRecurrences(method), Is.EqualTo(expected));
        Assert.That(sum.Type, Is.SameAs(expected ? type : null));
        if (expected)
        {
            Assert.That(next.Type, Is.SameAs(type));
            Assert.That(LocalVariables.PropagateIntegerRecurrences(method), Is.False);
        }
    }
}
