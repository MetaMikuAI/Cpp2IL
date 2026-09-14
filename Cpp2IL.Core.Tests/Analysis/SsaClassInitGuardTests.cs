using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class SsaClassInitGuardTests
{
    [TestCase(false)]
    [TestCase(true)]
    public void RemovesTypedFlagGuardAndRepairsClassPhi(bool inverted) => Check(inverted, "none", true);

    [TestCase("offset")]
    [TestCase("mask")]
    [TestCase("receiver")]
    [TestCase("untyped")]
    [TestCase("managed")]
    [TestCase("store")]
    [TestCase("polarity")]
    [TestCase("extraCall")]
    public void RetainsNonInitializerBranches(string mutation) => Check(false, mutation, false);

    private static void Check(bool inverted, string mutation, bool shouldRemove)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var type = app.SystemTypes.SystemStringType;
        var runtimeClass = new RuntimeClassTypeAnalysisContext(type, type.DeclaringAssembly);
        LocalVariable Local(string name, TypeAnalysisContext? t = null) => new(name, new Register(null, name), t);
        var klass = Local("klass", mutation == "untyped" ? null : runtimeClass);
        var flag = Local("flag");
        var masked = Local("masked");
        var zero = Local("zero", app.SystemTypes.SystemBooleanType);
        var not = Local("not", app.SystemTypes.SystemBooleanType);
        var argument = Local("argument", runtimeClass);
        var initialized = Local("initialized", runtimeClass);
        var merged = Local("merged", runtimeClass);
        var load = new Instruction(0, OpCode.Move, flag, new MemoryOperand(klass, addend: mutation == "offset" ? 0x134 : 0x135));
        var phi = new Instruction(20, OpCode.Phi, merged, klass, initialized);
        var prepare = new Instruction(10, OpCode.Move, argument, mutation == "receiver" ? Local("other", runtimeClass) : klass);
        IOperand target = mutation == "managed"
            ? new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Managed", app.SystemTypes.SystemVoidType,
                MethodAttributes.Public | MethodAttributes.Static, [])
            : new Immediate(0x1234);
        var call = new Instruction(11, OpCode.Call, target, initialized, argument);
        var guard = new Instruction(4, OpCode.ConditionalJump, inverted ^ mutation == "polarity" ? phi : prepare, inverted ? not : zero);
        var instructions = new List<Instruction>
        {
            load,
            new(1, OpCode.And, masked, flag, new Immediate(mutation == "mask" ? 2 : 1)),
            new(2, OpCode.CheckEqual, zero, masked, new Immediate(0)),
            new(3, OpCode.Not, not, zero),
            guard,
        };
        var branchToMerge = inverted ^ mutation == "polarity";
        if (!branchToMerge)
        {
            instructions.Add(phi);
            instructions.Add(new(21, OpCode.Return, merged));
        }
        instructions.Add(prepare);
        instructions.Add(call);
        if (mutation == "store") instructions.Add(new(12, OpCode.Move, new MemoryOperand(klass), new Immediate(1)));
        if (mutation == "extraCall") instructions.Add(new(13, OpCode.CallVoid, new Immediate(0x4321), argument));
        instructions.Add(new(14, OpCode.Jump, phi));
        if (branchToMerge)
        {
            instructions.Add(phi);
            instructions.Add(new(21, OpCode.Return, merged));
        }
        if (!branchToMerge) instructions.Add(new(100, OpCode.Return, merged));
        var graph = new ISILControlFlowGraph(instructions);
        graph.RemoveUnreachableBlocks();
        graph.MergeCallBlocks();
        var mergeBlock = graph.Blocks.Single(b => b.Instructions.Contains(phi));
        phi.SetOperands(new IOperand[] { merged }.Concat(mergeBlock.Predecessors.Select(b => b.Instructions.Contains(call) ? initialized : klass)).ToList());
        MetadataInitGuardRemover.RunSsaClassGuards(graph, 0x135);
        Assert.That(graph.Instructions.Contains(call), Is.EqualTo(!shouldRemove));
        if (shouldRemove)
        {
            Assert.That(phi.Operands, Is.EqualTo(new IOperand[] { merged, klass }));
            Assert.That(graph.Instructions.Any(i => i.Operands.Any(o => o is MemoryOperand)), Is.False);
        }
        MetadataInitGuardRemover.RunSsaClassGuards(graph, 0x135);
        Assert.That(graph.Instructions.Contains(call), Is.EqualTo(!shouldRemove));
    }
}
