using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class PartialStructLoadTests
{
    [TestCase("nested", false, true)]
    [TestCase("nested", true, true)]
    [TestCase("direct", false, true)]
    [TestCase("unknownWidth", false, false)]
    [TestCase("wholeCopy", false, false)]
    [TestCase("wrongWidth", false, false)]
    [TestCase("explicit", false, false)]
    [TestCase("ambiguous", false, false)]
    [TestCase("sameSizedInner", false, false)]
    [TestCase("cycle", false, false)]
    [TestCase("generic", false, false)]
    [TestCase("aggregateConsumer", false, false)]
    [TestCase("aggregateCopyChain", false, false)]
    [TestCase("aggregatePhi", false, false)]
    public void RequiresPartialAccessAtEveryValueTypeLevel(string shape, bool is32Bit, bool expected)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        app.Binary.is32Bit = is32Bit;
        var pointerSize = app.Binary.PointerSizeBytes;
        var valueType = app.AllTypes.Single(t => t.FullName == "System.ValueType");
        var inner = new InjectedTypeAnalysisContext(valueType.DeclaringAssembly, "Tests", "TaskValue", valueType, TypeAttributes.Public);
        var source = new InjectedFieldAnalysisContext("source", app.SystemTypes.SystemObjectType, FieldAttributes.Public, inner, 0);
        inner.Fields.Add(source);
        inner.Fields.Add(new InjectedFieldAnalysisContext("token", app.SystemTypes.SystemInt32Type, FieldAttributes.Public, inner, pointerSize));
        var outer = new InjectedTypeAnalysisContext(valueType.DeclaringAssembly, "Tests", "Awaiter", valueType, TypeAttributes.Public);
        var task = new InjectedFieldAnalysisContext("task", inner, FieldAttributes.Public, outer, 0);
        outer.Fields.Add(task);
        var owner = app.AllTypes.Single(t => t.FullName == "UnityEngine.Object");
        var field = owner.Fields.Single(f => f.Name == "m_CachedPtr");
        field.FieldType = shape == "direct" ? inner : outer;
        switch (shape)
        {
            case "explicit": inner.Attributes |= TypeAttributes.ExplicitLayout; break;
            case "ambiguous": inner.Fields.Add(new InjectedFieldAnalysisContext("alias", app.SystemTypes.SystemInt64Type, FieldAttributes.Public, inner, 0)); break;
            case "sameSizedInner":
                inner.Fields.RemoveAt(1);
                outer.Fields.Add(new InjectedFieldAnalysisContext("other", app.SystemTypes.SystemInt32Type, FieldAttributes.Public, outer, pointerSize));
                break;
            case "cycle": source.FieldType = inner; break;
            case "generic": inner.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
                GenericParameterAttributes.None, inner)); break;
        }
        var width = shape switch { "unknownWidth" => 0, "wholeCopy" => 2 * pointerSize, "wrongWidth" => 1, _ => pointerSize };
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), owner);
        var result = new LocalVariable("result", new Register(null, "result"), shape == "aggregateConsumer" ? field.FieldType : null);
        var consumer = new LocalVariable("consumer", new Register(null, "consumer"), field.FieldType);
        var read = new Instruction(0, OpCode.Move, result, new MemoryOperand(receiver, addend: field.Offset, accessSize: width));
        var use = shape switch
        {
            "aggregateCopyChain" => new Instruction(1, OpCode.Move, consumer, result),
            "aggregatePhi" => new Instruction(1, OpCode.Phi, consumer, result, receiver),
            _ => new Instruction(1, OpCode.Nop)
        };
        var method = new InjectedMethodAnalysisContext(owner, "Read", app.SystemTypes.SystemVoidType, MethodAttributes.Static | MethodAttributes.Public, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([read, use, new(2, OpCode.Return)]),
            Locals = [receiver, result, consumer], ParameterLocals = []
        };
        MetadataResolver.ResolveFieldOffsets(method);
        var reference = (FieldReference)read.Operands[1];
        Assert.That(reference.IsNested, Is.EqualTo(expected));
        if (expected)
        {
            Assert.That(reference.Field, Is.SameAs(source));
            Assert.That(reference.ContainingFields, Is.EqualTo(shape == "direct"
                ? new FieldAnalysisContext[] { field } : new FieldAnalysisContext[] { field, task }));
        }
        else
            Assert.That(reference.Field, Is.SameAs(field), "Do not split whole copies or unproven layouts");
    }
}
