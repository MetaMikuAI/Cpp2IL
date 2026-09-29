using System.Collections.Generic;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class WholeValuePieceStoreRecoveryTests
{
    private ApplicationAnalysisContext app = null!;
    private TypeAnalysisContext pair = null!;
    private FieldAnalysisContext first = null!, second = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        app = Cpp2IlApi.CurrentAppContext!;
        var assembly = new InjectedAssemblyAnalysisContext("Pairs", app);
        var valueType = app.SystemTypes.SystemInt32Type.BaseType!;
        pair = new InjectedTypeAnalysisContext(assembly, "Tests", "Pair", valueType, TypeAttributes.Public | TypeAttributes.Sealed);
        first = new InjectedFieldAnalysisContext("first", app.SystemTypes.SystemObjectType, System.Reflection.FieldAttributes.Private, pair, 0);
        second = new InjectedFieldAnalysisContext("second", app.SystemTypes.SystemInt32Type, System.Reflection.FieldAttributes.Private, pair, 8);
        pair.Fields.Add(first);
        pair.Fields.Add(second);
    }

    private LocalVariable Local(string name, TypeAnalysisContext? type) => new(name, new Register(null, name), type);

    [TestCase("first", true)]
    [TestCase("second", false)]
    [TestCase("otherTarget", false)]
    public void FirstMemberOfAValueStoredIntoItsType_IsTheWholeValue(string kind, bool recovered)
    {
        var result = Local("result", pair);
        var target = Local("slot", kind == "otherTarget" ? app.SystemTypes.SystemObjectType : pair);
        var store = new Instruction(0, OpCode.Move, target, new FieldReference(kind == "second" ? second : first, result, kind == "second" ? 8 : 0));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Spill", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            Locals = [result, target], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph(new List<Instruction> { store, new(1, OpCode.Return) }),
        };

        Assert.That(WholeValuePieceStoreRecovery.Run(method), Is.EqualTo(recovered));
        Assert.That(store.Operands[1], recovered ? Is.SameAs(result) : Is.InstanceOf<FieldReference>());
    }
}
