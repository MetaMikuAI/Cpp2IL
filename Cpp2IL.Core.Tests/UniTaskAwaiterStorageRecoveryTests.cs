using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class UniTaskAwaiterStorageRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    [TestCase(false, true)]
    [TestCase(true, false)]
    public void AwaiterStoredFromTheTasksSource_IsGetAwaiter(bool taskWrittenBetween, bool recovered)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        // The fixture has no UniTask; mirror the members this recovery binds.
        var assembly = new InjectedAssemblyAnalysisContext("UniTask", app);
        var source = new InjectedTypeAnalysisContext(assembly, "Cysharp.Threading.Tasks", "IUniTaskSource", null, System.Reflection.TypeAttributes.Interface | System.Reflection.TypeAttributes.Public);
        var task = new InjectedTypeAnalysisContext(assembly, "Cysharp.Threading.Tasks", "UniTask", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var awaiter = new InjectedTypeAnalysisContext(assembly, "", "Awaiter", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.NestedPublic) { DeclaringType = task };
        var sourceField = new InjectedFieldAnalysisContext("source", source, System.Reflection.FieldAttributes.Assembly, task);
        task.Methods.Add(new InjectedMethodAnalysisContext(task, "GetAwaiter", awaiter, System.Reflection.MethodAttributes.Public, []));

        LocalVariable Local(string name, TypeAnalysisContext type) => new(name, new Register(null, name), type);
        var (returned, other, piece, copy, slot) = (Local("task", task), Local("other", task), Local("piece", source), Local("copy", source), Local("stack_-50", awaiter));
        List<Instruction> instructions = [new(0, OpCode.Move, piece, new FieldReference(sourceField, returned, 0))];
        if (taskWrittenBetween)
            instructions.Add(new Instruction(1, OpCode.Move, returned, other));
        var store = new Instruction(3, OpCode.Move, slot, copy);
        instructions.AddRange([new Instruction(2, OpCode.Move, copy, piece), store, new Instruction(4, OpCode.Return)]);
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "MoveNext", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
        {
            Locals = [returned, other, piece, copy, slot], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph(instructions),
        };

        Assert.That(UniTaskAwaiterStorageRecovery.Run(method), Is.EqualTo(recovered));
        if (!recovered)
            return;
        Assert.That(store.OpCode, Is.EqualTo(OpCode.Call));
        Assert.That(((MethodAnalysisContext)store.Operands[0]).Name, Is.EqualTo("GetAwaiter"));
        Assert.That(store.Operands[1], Is.EqualTo(slot));
        Assert.That(store.Operands[2] is AddressOf { Target: var t } && t == returned, "called on the task");
    }
}
