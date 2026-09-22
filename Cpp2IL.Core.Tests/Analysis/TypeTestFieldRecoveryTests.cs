using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class TypeTestFieldRecoveryTests
{
    private ApplicationAnalysisContext _app = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
    }

    private GenericInstanceTypeAnalysisContext Container(string name, TypeAnalysisContext argument)
    {
        var root = _app.SystemTypes.SystemObjectType;
        var type = new InjectedTypeAnalysisContext(root.DeclaringAssembly, "Tests", name, root, TypeAttributes.Public);
        var t = new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR, GenericParameterAttributes.None, type);
        type.GenericParameters.Add(t);
        type.Fields.Add(new InjectedFieldAnalysisContext("data", t, FieldAttributes.Public, type, 0));
        return type.MakeGenericInstanceType([argument]);
    }

    private (MethodAnalysisContext Method, Instruction Test, Instruction Success, Instruction Nested, Instruction Failure, Instruction Join)
        Create(string condition, string problem = "")
    {
        var root = _app.SystemTypes.SystemObjectType;
        var inner = Container("Inner`1", _app.SystemTypes.SystemInt32Type);
        var target = Container("Outer`1", inner);
        var source = new LocalVariable("source", new Register(null, "source"), root);
        var alias = new LocalVariable("alias", new Register(null, "alias"), root);
        var other = new LocalVariable("other", new Register(null, "other"), root);
        var result = new LocalVariable("matches", new Register(null, "matches"), _app.SystemTypes.SystemBooleanType);
        var predicate = new LocalVariable("condition", new Register(null, "condition"), _app.SystemTypes.SystemBooleanType);
        var cast = new LocalVariable("cast", new Register(null, "cast"), target);
        var child = new LocalVariable("child", new Register(null, "child"));
        var value = new LocalVariable("value", new Register(null, "value"));
        var failed = new LocalVariable("failed", new Register(null, "failed"));
        var joined = new LocalVariable("joined", new Register(null, "joined"));
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var test = new Instruction(0, OpCode.IsInstance, result, target, source);
        var success = new Instruction(10, OpCode.Move, child, new MemoryOperand(alias, addend: 16, accessSize: 8));
        var nested = new Instruction(11, OpCode.Move, value, new MemoryOperand(child, addend: 16, accessSize: 4));
        var failure = new Instruction(5, OpCode.Move, failed, new MemoryOperand(source, addend: 16, accessSize: 8));
        var join = new Instruction(20, OpCode.Move, joined, new MemoryOperand(source, addend: 16, accessSize: 8));
        var successEntry = new Instruction(9, OpCode.Move, alias, source);
        var list = new List<Instruction> { test };
        var positive = true;
        IOperand branchCondition = result;
        switch (condition)
        {
            case "not": list.Add(new(1, OpCode.Not, predicate, result)); positive = false; branchCondition = predicate; break;
            case "equalZero": list.Add(new(1, OpCode.CheckEqual, predicate, result, new Immediate(0))); positive = false; branchCondition = predicate; break;
            case "notEqualZero": list.Add(new(1, OpCode.CheckNotEqual, predicate, new Immediate(0), result)); branchCondition = predicate; break;
            case "cast":
                test.OpCode = OpCode.TryCast; test.SetOperands(cast, target, source);
                list.Add(new(1, OpCode.CheckNotEqual, predicate, cast, new Immediate(0))); branchCondition = predicate;
                break;
        }
        switch (problem)
        {
            case "valueType": test.SetOperand(1, _app.SystemTypes.SystemInt32Type); break;
            case "byrefType": test.SetOperand(1, new ByRefTypeAnalysisContext(root)); break;
            case "genericParameter": test.SetOperand(1, target.GenericType.GenericParameters[0]); break;
            case "interface":
                test.SetOperand(1, new InjectedTypeAnalysisContext(root.DeclaringAssembly, "Tests", "IValue", root,
                    TypeAttributes.Public | TypeAttributes.Interface | TypeAttributes.Abstract));
                break;
            case "otherObject": successEntry.SetOperand(1, other); break;
            case "reload":
                list.Insert(0, new(-1, OpCode.Move, source, new MemoryOperand(other, addend: 32)));
                successEntry.SetOperand(1, new MemoryOperand(other, addend: 32));
                break;
            case "sourceAddress": list.Add(new(2, OpCode.Move, pointer, new AddressOf(source))); break;
            case "aliasAddress": list.Add(new(2, OpCode.Move, pointer, new AddressOf(alias))); break;
            case "conditionAddress": list.Add(new(2, OpCode.Move, pointer, new AddressOf(branchCondition))); break;
        }
        if (positive)
        {
            list.Add(new(3, OpCode.ConditionalJump, successEntry, branchCondition));
            list.Add(failure);
            list.Add(new(6, OpCode.Jump, problem == "joinEntry" ? successEntry : join));
            list.Add(successEntry);
        }
        else
        {
            list.Add(new(3, OpCode.ConditionalJump, failure, branchCondition));
            list.Add(successEntry);
        }
        if (problem == "call")
            list.Add(new(8, OpCode.CallVoid, new InjectedMethodAnalysisContext(root, "Mutate", _app.SystemTypes.SystemVoidType,
                MethodAttributes.Public | MethodAttributes.Static, [])));
        list.AddRange([success, nested, new(12, OpCode.Jump, join)]);
        if (!positive) list.Add(failure);
        list.AddRange([join, new(21, OpCode.Return)]);
        var method = new InjectedMethodAnalysisContext(root, "Read", _app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph(list),
            Locals = [source, alias, other, result, predicate, cast, child, value, failed, joined, pointer], ParameterLocals = []
        };
        return (method, test, success, nested, failure, join);
    }

    [TestCase("direct")]
    [TestCase("not")]
    [TestCase("equalZero")]
    [TestCase("notEqualZero")]
    [TestCase("cast")]
    public void RefinesOnlyTheSuccessfulEdgeAndResolvesNestedFields(string condition)
    {
        var (method, test, success, nested, failure, join) = Create(condition);
        Assert.That(TypeTestFieldRecovery.Run(method), Is.True);
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(test.OpCode, Is.EqualTo(OpCode.TryCast));
        Assert.That(success.Operands[1], Is.TypeOf<FieldReference>());
        Assert.That(nested.Operands[1], Is.TypeOf<FieldReference>());
        Assert.That(((LocalVariable)nested.Destination!).Type, Is.SameAs(_app.SystemTypes.SystemInt32Type));
        Assert.That(failure.Operands[1], Is.TypeOf<MemoryOperand>());
        Assert.That(join.Operands[1], Is.TypeOf<MemoryOperand>());
        Assert.That(((LocalVariable)test.Operands[2]).Type, Is.SameAs(_app.SystemTypes.SystemObjectType));
        Assert.That(TypeTestFieldRecovery.Run(method), Is.False);
    }

    [TestCase("valueType")]
    [TestCase("byrefType")]
    [TestCase("genericParameter")]
    [TestCase("interface")]
    [TestCase("otherObject")]
    [TestCase("reload")]
    [TestCase("sourceAddress")]
    [TestCase("aliasAddress")]
    [TestCase("conditionAddress")]
    [TestCase("joinEntry")]
    public void DoesNotInferATypeWithoutAStableObjectAndProvenSuccessEdge(string problem)
    {
        var (method, test, success, _, _, _) = Create("direct", problem);
        Assert.That(TypeTestFieldRecovery.Run(method), Is.False);
        Assert.That(test.OpCode, Is.EqualTo(OpCode.IsInstance));
        Assert.That(success.Operands[1], Is.TypeOf<MemoryOperand>());
    }

    [Test]
    public void ACallCannotChangeTheRuntimeTypeOfTheCapturedReference()
    {
        var (method, _, success, _, _, _) = Create("direct", "call");
        Assert.That(TypeTestFieldRecovery.Run(method), Is.True);
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(success.Operands[1], Is.TypeOf<FieldReference>());
    }
}
