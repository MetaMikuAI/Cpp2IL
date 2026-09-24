using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class AggregateCopyRecoveryTests
{
    private ApplicationAnalysisContext _app = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
    }

    private (MethodAnalysisContext Method, List<Instruction> Loads, List<Instruction> Stores) Copy(
        string typeName = "UnityEngine.Bounds", bool inherited = false, bool generic = true)
    {
        var valueType = _app.AllTypes.Single(t => t.FullName == typeName);
        var root = _app.SystemTypes.SystemObjectType;
        TypeAnalysisContext owner;
        long offset;
        if (generic)
        {
            var definition = new InjectedTypeAnalysisContext(root.DeclaringAssembly, "Tests", "Container`1", root, TypeAttributes.Public);
            var parameter = new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
                GenericParameterAttributes.None, definition);
            definition.GenericParameters.Add(parameter);
            definition.Fields.Add(new InjectedFieldAnalysisContext("data", parameter, FieldAttributes.Public, definition, 0));
            owner = definition.MakeGenericInstanceType([valueType]);
            offset = 2 * _app.Binary.PointerSizeBytes;
        }
        else
        {
            owner = _app.AllTypes.Single(t => t.FullName == "UnityEngine.Object");
            var field = owner.Fields.Single(f => f.Name == "m_CachedPtr");
            field.FieldType = valueType;
            offset = field.Offset;
        }
        if (inherited)
            owner = new InjectedTypeAnalysisContext(root.DeclaringAssembly, "Tests", "Derived", owner, TypeAttributes.Public);
        var receiver = new LocalVariable("this", new Register(null, "X0"), owner) { IsThis = true };
        var source = new LocalVariable("param_0", new Register(null, "X1"), valueType);
        var locals = new List<LocalVariable> { receiver, source };
        var loads = new List<Instruction>();
        var stores = new List<Instruction>();
        var size = valueType.Definition!.RawSizes.instance_size - 2 * _app.Binary.PointerSizeBytes;
        for (var i = 0; i < size; i += 16)
        {
            var width = (int)System.Math.Min(16, size - i);
            var chunk = new LocalVariable($"chunk{i}", new Register(null, $"V{i}"));
            locals.Add(chunk);
            loads.Add(new Instruction(loads.Count, OpCode.Move, chunk, new MemoryOperand(source, addend: i, accessSize: width)));
            stores.Add(new Instruction(100 + stores.Count, OpCode.Move, new MemoryOperand(receiver, addend: offset + i, accessSize: width), chunk));
        }
        stores.Reverse();
        var method = new InjectedMethodAnalysisContext(owner, "Copy", _app.SystemTypes.SystemVoidType,
            MethodAttributes.Public, [valueType])
        {
            Locals = locals, ParameterLocals = [receiver, source],
            ControlFlowGraph = new ISILControlFlowGraph([.. loads, new(90, OpCode.Nop), .. stores, new(200, OpCode.Return)])
        };
        return (method, loads, stores);
    }

    [TestCase("UnityEngine.Bounds", false, true)]
    [TestCase("UnityEngine.Bounds", true, true)]
    [TestCase("UnityEngine.Matrix4x4", false, true)]
    [TestCase("UnityEngine.Bounds", false, false)]
    [TestCase("UnityEngine.Bounds", true, false)]
    public void RecoversCompleteCopyBeforeMemberTypePropagation(string typeName, bool inherited, bool generic)
    {
        var (method, loads, stores) = Copy(typeName, inherited, generic);
        LocalVariables.ResolveTypesAndFields(method);
        var assignments = method.ControlFlowGraph!.Instructions.Where(i => i.OpCode == OpCode.Move).ToList();
        Assert.That(assignments, Has.Count.EqualTo(1));
        Assert.That(assignments[0], Is.SameAs(stores[0]));
        var field = (FieldReference)assignments[0].Operands[0];
        Assert.That(field.IsNested, Is.False);
        Assert.That(field.Field.FieldType, Is.SameAs(method.ParameterLocals[1].Type));
        if (generic)
            Assert.That(field.Field, Is.TypeOf<ConcreteGenericFieldAnalysisContext>());
        Assert.That(assignments[0].Operands[1], Is.SameAs(method.ParameterLocals[1]));
        Assert.That(loads.All(i => i.OpCode == OpCode.Nop), Is.True);
        Assert.That(AggregateCopyRecovery.Run(method), Is.False);
    }

    [TestCase("missing")]
    [TestCase("gap")]
    [TestCase("overlap")]
    [TestCase("overrun")]
    [TestCase("width")]
    [TestCase("type")]
    [TestCase("notParameter")]
    [TestCase("byref")]
    [TestCase("call")]
    [TestCase("read")]
    [TestCase("write")]
    [TestCase("extraUse")]
    [TestCase("addressEscape")]
    [TestCase("interleaved")]
    [TestCase("crossBlock")]
    [TestCase("unknownWidth")]
    public void RejectsIncompleteOrObservableCopy(string problem)
    {
        var (method, loads, stores) = Copy();
        var list = method.ControlFlowGraph!.Blocks.Single(b => b.Instructions.Contains(loads[0])).Instructions;
        var source = method.ParameterLocals[1];
        var firstRead = (MemoryOperand)loads[0].Operands[1];
        var firstWrite = (MemoryOperand)stores[^1].Operands[0];
        var temp = new LocalVariable("extra", new Register(null, "extra"));
        switch (problem)
        {
            case "missing": list.Remove(stores[0]); break;
            case "gap": firstRead.Addend++; firstWrite.Addend++; break;
            case "overlap":
                var read = (MemoryOperand)loads[1].Operands[1]; read.Addend--;
                var write = (MemoryOperand)stores[0].Operands[0]; write.Addend--;
                loads[1].SetOperand(1, read); stores[0].SetOperand(0, write);
                break;
            case "overrun": firstRead.AccessSize++; firstWrite.AccessSize++; break;
            case "width": firstWrite.AccessSize--; break;
            case "unknownWidth": firstRead.AccessSize = 0; firstWrite.AccessSize = 0; break;
            case "type": ((GenericInstanceTypeAnalysisContext)method.DeclaringType!).GenericType.Fields[0].FieldType = _app.SystemTypes.SystemInt64Type; break;
            case "notParameter": method.ParameterLocals.Remove(source); break;
            case "byref": source.Type = new ByRefTypeAnalysisContext(source.Type!); break;
            case "call": list.Insert(loads.Count, new(80, OpCode.CallVoid, new Immediate(123))); break;
            case "read": list.Insert(loads.Count, new(80, OpCode.Move, temp, new MemoryOperand(source, accessSize: 4))); break;
            case "write": list.Insert(loads.Count, new(80, OpCode.Move, new MemoryOperand(source, accessSize: 4), new Immediate(0))); break;
            case "extraUse": list.Insert(0, new(80, OpCode.Move, temp, loads[0].Operands[0])); break;
            case "addressEscape": list.Insert(0, new(80, OpCode.Move, temp, new AddressOf(loads[0].Operands[0]))); break;
            case "interleaved": list.Remove(stores[0]); list.Insert(0, stores[0]); break;
            case "crossBlock":
                method.ControlFlowGraph = new ISILControlFlowGraph([.. loads, new(80, OpCode.Jump, stores[0]), .. stores, new(200, OpCode.Return)]);
                break;
        }
        loads[0].SetOperand(1, firstRead);
        stores[^1].SetOperand(0, firstWrite);
        Assert.That(AggregateCopyRecovery.Run(method), Is.False);
        Assert.That(stores.All(i => i.OpCode == OpCode.Move), Is.True);
        Assert.That(loads.All(i => i.OpCode == OpCode.Move), Is.True);
    }
    [TestCase("ok", true)]
    [TestCase("missing", false)]
    [TestCase("overlap", false)]
    [TestCase("extraUse", false)]
    [TestCase("call", false)]
    [TestCase("wrongBuffer", false)]
    [TestCase("wrongType", false)]
    public void RecoversOnlyCompleteUnobservedFieldToReturnBufferCopy(string problem, bool expected)
    {
        var (method, loads, stores) = Copy(generic: false);
        _app.InstructionSet = new InstructionSets.NewArmV8InstructionSet();
        var owner = method.ParameterLocals[0];
        var type = method.ParameterLocals[1].Type!;
        var field = owner.Type!.Fields.Single(f => f.Name == "m_CachedPtr");
        var buffer = new LocalVariable("returnBuffer", new Register(null, "X8", -1), type);
        var targetMethod = new InjectedMethodAnalysisContext(owner.Type, "Get", type, MethodAttributes.Public, [])
        {
            Locals = [owner, buffer, .. loads.Select(l => (LocalVariable)l.Operands[0])],
            ParameterLocals = [owner]
        };
        foreach (var load in loads)
        {
            var memory = (MemoryOperand)load.Operands[1];
            memory.Base = owner;
            memory.Addend += field.Offset;
            load.SetOperand(1, memory);
        }
        foreach (var store in stores)
        {
            var memory = (MemoryOperand)store.Operands[0];
            memory.Base = problem == "wrongBuffer" ? owner : buffer;
            memory.Addend -= field.Offset;
            store.SetOperand(0, memory);
        }
        List<Instruction> instructions = [.. loads, .. stores, new(200, OpCode.Return, buffer)];
        switch (problem)
        {
            case "missing": instructions.Remove(stores[0]); break;
            case "overlap":
                var read = (MemoryOperand)loads[1].Operands[1]; read.Addend--;
                var write = (MemoryOperand)stores[0].Operands[0]; write.Addend--;
                loads[1].SetOperand(1, read); stores[0].SetOperand(0, write);
                break;
            case "extraUse": instructions.Insert(0, new(80, OpCode.Move, owner, loads[0].Operands[0])); break;
            case "call": instructions.Insert(loads.Count, new(80, OpCode.CallVoid, new Immediate(123))); break;
            case "wrongType": field.FieldType = _app.SystemTypes.SystemInt32Type; break;
        }
        targetMethod.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        Assert.That(AggregateCopyRecovery.Run(targetMethod), Is.EqualTo(expected));
        if (expected)
        {
            Assert.That(stores[0].Operands[0], Is.SameAs(buffer));
            var source = (FieldReference)stores[0].Operands[1];
            Assert.That(source.Local, Is.SameAs(owner));
            Assert.That(source.Field, Is.SameAs(field));
            Assert.That(loads.All(l => l.OpCode == OpCode.Nop), Is.True);
            Assert.That(AggregateCopyRecovery.Run(targetMethod), Is.False);
        }
    }
}
