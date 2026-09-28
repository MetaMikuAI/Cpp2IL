using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class InlinedListClearRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    [TestCase("values", true)]
    [TestCase("valuesReadBetween", false)]
    [TestCase("referencesWithoutArrayClear", false)]
    [TestCase("join", true)]
    [TestCase("return", true)]
    [TestCase("joinOtherCount", false)]
    public void InlinedClear_IsRecoveredOnlyForTheExactShape(string shape, bool recovered)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = app.AllTypes.Single(t => t.FullName == "System.Collections.Generic.List`1");
        var references = shape is not ("values" or "valuesReadBetween");
        var element = references ? app.SystemTypes.SystemStringType : app.SystemTypes.SystemInt32Type;
        var instance = new GenericInstanceTypeAnalysisContext(owner, [element]);
        FieldReference Field(LocalVariable local, string name)
            => new(new ConcreteGenericFieldAnalysisContext(owner.Fields.Single(f => f.Name == name), instance), local, 0);
        LocalVariable Local(string name, TypeAnalysisContext type) => new(name, new Register(null, name), type);

        var list = Local("list", instance);
        var size = Local("size", app.SystemTypes.SystemInt32Type);
        var version = Local("version", app.SystemTypes.SystemInt32Type);
        var nextVersion = Local("nextVersion", app.SystemTypes.SystemInt32Type);
        var empty = Local("empty", app.SystemTypes.SystemBooleanType);
        var observed = Local("observed", app.SystemTypes.SystemInt32Type);
        var other = Local("other", app.SystemTypes.SystemInt32Type);
        var items = Local("items", element.MakeSzArrayType());
        var arrayClear = app.AllTypes.Single(t => t.FullName == "System.Array").Methods
            .First(m => m is { Name: "Clear", IsStatic: true, Parameters.Count: 3 });

        var end = new Instruction(20, OpCode.Return);
        List<Instruction> instructions =
        [
            new(0, OpCode.Move, size, Field(list, "_size")),
            new(1, OpCode.Move, version, Field(list, "_version")),
            new(2, OpCode.Add, nextVersion, version, new Immediate(1)),
            new(3, OpCode.Move, Field(list, "_size"), new Immediate(0)),
        ];
        if (shape == "valuesReadBetween")
            instructions.Add(new Instruction(4, OpCode.Move, observed, Field(list, "_size")));
        instructions.Add(new Instruction(5, OpCode.Move, Field(list, "_version"), nextVersion));
        if (shape is "join" or "return" or "joinOtherCount")
        {
            instructions.Add(new Instruction(6, OpCode.CheckLess, empty, size, new Immediate(1)));
            var jump = new Instruction(7, OpCode.ConditionalJump, end, empty);
            instructions.Add(jump);
            // The arm loads the items itself.
            instructions.Add(new Instruction(8, OpCode.Move, items, Field(list, "_items")));
            instructions.Add(new Instruction(8, OpCode.CallVoid, arrayClear, items, new Immediate(0), shape == "joinOtherCount" ? other : size));
            if (shape == "return")
            {
                var skip = new Instruction(10, OpCode.Return);
                jump.SetOperands(skip, empty);
                instructions.AddRange([new Instruction(9, OpCode.Return), skip]);
            }
        }
        if (shape != "return")
            instructions.Add(end);
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
        {
            Locals = [list, size, version, nextVersion, empty, observed, other, items], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph(instructions),
        };
        method.ControlFlowGraph.MergeCallBlocks();

        Assert.That(InlinedListClearRecovery.Run(method), Is.EqualTo(recovered));

        var remaining = method.ControlFlowGraph.Blocks.SelectMany(b => b.Instructions).Where(i => i.OpCode != OpCode.Nop).ToList();
        if (!recovered)
        {
            Assert.That(remaining.Any(i => i.Operands.FirstOrDefault() is FieldReference { Field.Name: "_version" }), Is.True);
            return;
        }
        var call = remaining.Single(i => i.OpCode == OpCode.CallVoid);
        Assert.That(((MethodAnalysisContext)call.Operands[0]).Name, Is.EqualTo("Clear"));
        Assert.That(((ConcreteGenericMethodAnalysisContext)call.Operands[0]).TypeGenericParameters, Is.EqualTo(new[] { element }));
        Assert.That(call.Operands.Skip(1), Is.EqualTo(new IOperand[] { list }));
        Assert.That(remaining.Any(i => i.Operands.Any(o => o is FieldReference)), Is.False, "the inlined body and its loads are gone");
        Assert.That(remaining.Count(i => i.OpCode == OpCode.Return), Is.EqualTo(1));
    }
}
