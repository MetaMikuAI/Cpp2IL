using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class UniTaskReturnRecoveryTests
{
    private ApplicationAnalysisContext app = null!;
    private TypeAnalysisContext task = null!, source = null!;
    private FieldAnalysisContext sourceField = null!, tokenField = null!;
    private MethodAnalysisContext returnsTask = null!, forget = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        app = Cpp2IlApi.CurrentAppContext!;
        // The fixture has no UniTask; mirror the members this recovery binds.
        var assembly = new InjectedAssemblyAnalysisContext("UniTask", app);
        source = new InjectedTypeAnalysisContext(assembly, "Cysharp.Threading.Tasks", "IUniTaskSource", null, TypeAttributes.Interface | TypeAttributes.Public);
        task = new InjectedTypeAnalysisContext(assembly, "Cysharp.Threading.Tasks", "UniTask", app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        sourceField = new InjectedFieldAnalysisContext("source", source, FieldAttributes.Private, task, 0);
        tokenField = new InjectedFieldAnalysisContext("token", app.SystemTypes.SystemInt16Type, FieldAttributes.Private, task, 8);
        task.Fields.Add(sourceField);
        task.Fields.Add(tokenField);
        returnsTask = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "OnExiting", task, MethodAttributes.Public | MethodAttributes.Static, []);
        forget = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Forget", app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, [task]);
    }

    private LocalVariable Local(string name, TypeAnalysisContext? type) => new(name, new Register(null, name), type);

    [TestCase("whole", true)]
    [TestCase("usedElsewhere", false)]
    [TestCase("missingToken", false)]
    public void TaskStoredFromTheReturnRegisters_IsTheReturnedTask(string kind, bool recovered)
    {
        var returned = Local("returned", source);
        var built = Local("built", task);
        var stale = Local("stale", app.SystemTypes.SystemInt16Type);
        var keep = Local("keep", source);
        var call = new Instruction(0, OpCode.Call, returnsTask, returned);
        var instructions = new List<Instruction>
        {
            call,
            new(1, OpCode.Nop),
            new(2, OpCode.Move, new FieldReference(sourceField, built, 0), returned),
        };
        if (kind != "missingToken")
            instructions.Add(new(3, OpCode.Move, new FieldReference(tokenField, built, 8), stale));
        if (kind == "usedElsewhere")
            instructions.Add(new(4, OpCode.Move, keep, returned));
        instructions.Add(new(5, OpCode.CallVoid, forget, built));
        instructions.Add(new(6, OpCode.Return));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "OnExit", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            Locals = [returned, built, stale, keep], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph(instructions),
        };
        method.ControlFlowGraph.MergeCallBlocks();

        Assert.That(UniTaskReturnRecovery.Run(method), Is.EqualTo(recovered));
        Assert.That(call.Operands[1], Is.SameAs(recovered ? built : returned));
        var stores = method.ControlFlowGraph.Instructions.Count(i => i.Destination is FieldReference);
        Assert.That(stores, Is.EqualTo(recovered ? 0 : instructions.Count(i => i.Destination is FieldReference)));
    }
}
