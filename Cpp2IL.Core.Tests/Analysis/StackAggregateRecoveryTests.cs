using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class StackAggregateRecoveryTests
{
    private MethodAnalysisContext _method = null!;
    private TypeAnalysisContext _type = null!;
    private readonly HashSet<Instruction> _zeros = [];

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var definition = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "Tests", "Storage`1", app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType"), TypeAttributes.Public);
        definition.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            GenericParameterAttributes.None, definition));
        foreach (var name in new[] { "First", "Second", "Third" })
            definition.Fields.Add(new InjectedFieldAnalysisContext(name, definition.GenericParameters[0], FieldAttributes.Public, definition, 0));
        _type = definition.MakeGenericInstanceType([app.SystemTypes.SystemObjectType]);
        Assert.That(TypeSizes.UnboxedSize(_type, 8), Is.GreaterThan(16));
        _method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, []) { ParameterOperands = [] };
        _zeros.Clear();
    }

    private Instruction Zero(int offset, int width)
    {
        var zero = new Instruction(offset, OpCode.Move, new StackOffset(offset, width), new Immediate(0));
        _zeros.Add(zero);
        return zero;
    }

    [Test]
    public void StoresAndRepeatedAddressTakesShareStorageAcrossSsaAndDce()
    {
        var size = (int)TypeSizes.UnboxedSize(_type, 8);
        var instructions = Enumerable.Range(0, size / 8).Select(i => Zero(i * 8, 8)).ToList();
        var consume = new InjectedMethodAnalysisContext(_type, "Consume", _method.AppContext.SystemTypes.SystemVoidType,
            MethodAttributes.Public, []);
        instructions.Add(new(100, OpCode.CallVoid, consume, new AddressOf(new StackOffset(0))));
        instructions.Add(Zero(0, 8));
        instructions.Add(new(101, OpCode.CallVoid, consume, new AddressOf(new StackOffset(0))));
        instructions.Add(new(102, OpCode.Return));
        _method.ControlFlowGraph = new(instructions);
        StackAggregateRecovery.Recover(_method, [(0, _type)], _zeros);
        Assert.That(_method.StackAggregates.Count, Is.EqualTo(1));
        _method.DominatorInfo = new DominatorInfo(_method.ControlFlowGraph);
        SsaForm.Build(_method);
        LocalVariables.CreateAll(_method);
        DeadCodeEliminator.Run(_method);
        var stores = _method.ControlFlowGraph.Instructions.Where(i => i is { OpCode: OpCode.Move, Operands: [FieldReference, _] }).ToList();
        Assert.That(stores.Count, Is.EqualTo(size / 8 + 1));
        var owners = stores.Select(i => ((FieldReference)i.Operands[0]).Local).Distinct().ToList();
        Assert.That(owners.Count, Is.EqualTo(1));
        Assert.That(owners[0].Type, Is.SameAs(_type));
        foreach (var call in _method.ControlFlowGraph.Instructions.Where(i => i.IsCall))
            Assert.That(((AddressOf)call.Operands[1]).Target, Is.SameAs(owners[0]));
        _method.ReleaseAnalysisData();
        Assert.That(_method.StackAggregates, Is.Empty);
    }

    [TestCase("partial")]
    [TestCase("unknownWidth")]
    [TestCase("overlap")]
    [TestCase("nonzeroWideStore")]
    public void RejectsUnprovenStorageWithoutPartialMutation(string reason)
    {
        var instruction = Zero(0, reason == "partial" ? 4 : reason == "unknownWidth" ? 0 : 16);
        if (reason == "nonzeroWideStore") { _zeros.Clear(); instruction.SetOperand(1, new Immediate(42)); }
        _method.ControlFlowGraph = new([instruction, new(20, OpCode.Return)]);
        var roots = new List<(int, TypeAnalysisContext)> { (0, _type) };
        if (reason == "overlap") roots.Add((8, _type));
        StackAggregateRecovery.Recover(_method, roots, _zeros);
        Assert.That(_method.StackAggregates, Is.Empty);
        Assert.That(instruction.Operands[0], Is.TypeOf<StackOffset>());
    }

    [Test]
    public void MultipleDisjointAggregatesDoNotReprocessAlreadyExpandedStores()
    {
        _method.ControlFlowGraph = new([Zero(0, 16), Zero(32, 16), new(100, OpCode.Return)]);
        StackAggregateRecovery.Recover(_method, [(0, _type), (32, _type)], _zeros);
        Assert.That(_method.StackAggregates.Count, Is.EqualTo(2));
        Assert.That(_method.ControlFlowGraph.Instructions.Count(i => i.Destination is MemoryOperand), Is.EqualTo(4));
    }

    [Test]
    public void GenericSharedReceiverIsNotProofOfTheCallersStorageType()
    {
        var original = _method.AppContext.InstructionSet;
        try
        {
            _method.AppContext.InstructionSet = new NewArmV8InstructionSet();
            var receiver = new Register(null, "X0");
            var consume = new InjectedMethodAnalysisContext(_type, "Consume", _method.AppContext.SystemTypes.SystemVoidType,
                MethodAttributes.Public, []);
            var store = Zero(0, 16);
            _method.ControlFlowGraph = new([new(0, OpCode.Move, receiver, new AddressOf(new StackOffset(0))), store,
                new(10, OpCode.CallVoid, consume, receiver), new(11, OpCode.Return)]);
            StackAggregateRecovery.Run(_method);
            Assert.That(_method.StackAggregates, Is.Empty);
            Assert.That(store.Operands[0], Is.TypeOf<StackOffset>());
        }
        finally { _method.AppContext.InstructionSet = original; }
    }
}
