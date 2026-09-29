using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class ByRefFieldAccessRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    [TestCase(true)]
    [TestCase(false)]
    public void FieldOfAnotherTypeThroughAByRef_IsTheReferent(bool unrelated)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var assembly = new InjectedAssemblyAnalysisContext("Owner", app);
        var other = new InjectedTypeAnalysisContext(assembly, "", "TileData", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var flag = new InjectedFieldAnalysisContext("_allocate", app.SystemTypes.SystemBooleanType, System.Reflection.FieldAttributes.Private, other);
        var referent = unrelated ? app.SystemTypes.SystemBooleanType : (TypeAnalysisContext)other;
        var byRef = new LocalVariable("isDummy", new Register(null, "isDummy"), new ByRefTypeAnalysisContext(referent));
        var store = new Instruction(0, OpCode.Move, new FieldReference(flag, byRef, 0), new Immediate(0));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
        {
            Locals = [byRef], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph([store, new Instruction(1, OpCode.Return)]),
        };

        Assert.That(ByRefFieldAccessRecovery.Run(method), Is.EqualTo(unrelated));
        Assert.That(store.Operands[0] is MemoryOperand { Base: var b } && b == byRef, Is.EqualTo(unrelated));
    }
}
