using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class FieldLoadTypePropagationTests
{
    [TestCase("reference", true)]
    [TestCase("multiple", false)]
    [TestCase("value", false)]
    [TestCase("pointer", false)]
    [TestCase("byref", false)]
    public void ObjectCallDoesNotEraseSingleDefinitionFieldType(string scenario, bool expected)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var root = app.SystemTypes.SystemObjectType;
        var owner = new InjectedTypeAnalysisContext(root.DeclaringAssembly, "Tests", "Owner", root, TypeAttributes.Public);
        var valueType = scenario switch
        {
            "value" => app.SystemTypes.SystemInt32Type,
            "pointer" => new PointerTypeAnalysisContext(root),
            "byref" => new ByRefTypeAnalysisContext(root),
            _ => app.SystemTypes.SystemStringType
        };
        var field = new InjectedFieldAnalysisContext("Value", valueType, FieldAttributes.Public, owner, 16);
        owner.Fields.Add(field);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), owner);
        var value = new LocalVariable("value", new Register(null, "value"));
        var sink = new InjectedMethodAnalysisContext(root, "Use", app.SystemTypes.SystemVoidType,
            MethodAttributes.Static | MethodAttributes.Public, [root]);
        var method = new InjectedMethodAnalysisContext(root, "Caller", app.SystemTypes.SystemVoidType,
            MethodAttributes.Static | MethodAttributes.Public, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([
                new(0, OpCode.Move, value, new FieldReference(field, receiver, 16)),
                scenario == "multiple" ? new(1, OpCode.Move, value, new Immediate(0)) : new(1, OpCode.Nop),
                new(2, OpCode.CallVoid, sink, value), new(3, OpCode.Return)]),
            Locals = [receiver, value], ParameterLocals = []
        };
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(value.Type, Is.SameAs(expected ? valueType : root));
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(value.Type, Is.SameAs(expected ? valueType : root), "Type inference must settle");
    }
}
