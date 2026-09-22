using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Model.CustomAttributes;

namespace Cpp2IL.Core.Tests.Analysis;

public class RedundantFieldStoreEliminationTests
{
    [TestCase("adjacent", true)]
    [TestCase("nop", true)]
    [TestCase("call", false)]
    [TestCase("read", false)]
    [TestCase("otherReceiver", false)]
    [TestCase("otherOffset", false)]
    [TestCase("public", false)]
    [TestCase("userType", false)]
    [TestCase("branch", false)]
    public void RemovesOnlyUnobservedOverwrittenGeneratedStorage(string shape, bool expected)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var root = app.SystemTypes.SystemObjectType;
        var owner = new InjectedTypeAnalysisContext(root.DeclaringAssembly, "Tests", "Generated", root, TypeAttributes.Public);
        if (shape != "userType")
        {
            var attribute = new InjectedTypeAnalysisContext(root.DeclaringAssembly, "System.Runtime.CompilerServices", "CompilerGeneratedAttribute", root, TypeAttributes.Public);
            owner.CustomAttributes = [new AnalyzedCustomAttribute(attribute.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType, MethodAttributes.Public))];
        }
        var field = new InjectedFieldAnalysisContext("state", app.SystemTypes.SystemInt32Type,
            shape == "public" ? FieldAttributes.Public : FieldAttributes.Private, owner, 16);
        var receiver = new LocalVariable("this", new Register(null, "X0"), owner);
        var other = new LocalVariable("other", new Register(null, "X1"), owner);
        var first = new Instruction(0, OpCode.Move, new FieldReference(field, receiver, 16), new Immediate(-1));
        var second = new Instruction(2, OpCode.Move,
            new FieldReference(field, shape == "otherReceiver" ? other : receiver, shape == "otherOffset" ? 20 : 16), new Immediate(1));
        var between = shape switch
        {
            "call" => new Instruction(1, OpCode.CallVoid, new Immediate(123)),
            "read" => new Instruction(1, OpCode.Move, other, new FieldReference(field, receiver, 16)),
            "branch" => new Instruction(1, OpCode.Jump, second),
            _ => new Instruction(1, OpCode.Nop)
        };
        var method = new InjectedMethodAnalysisContext(owner, "Run", app.SystemTypes.SystemVoidType, MethodAttributes.Public, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([first, between, second, new Instruction(3, OpCode.Return)])
        };
        RedundantFieldStoreElimination.Run(method);
        Assert.That(first.OpCode == OpCode.Nop, Is.EqualTo(expected));
        Assert.That(second.OpCode, Is.EqualTo(OpCode.Move));
    }
}
