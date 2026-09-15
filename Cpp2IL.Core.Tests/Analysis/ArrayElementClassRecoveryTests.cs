using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ArrayElementClassRecoveryTests
{
    [TestCase("newarr", true)]
    [TestCase("helper", true)]
    [TestCase("parameter", false)]
    [TestCase("mixed", false)]
    [TestCase("wrong_offset", false)]
    public void RequiresExactArrayClassRatherThanCovariantStaticType(string kind, bool expected)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var actual = new SzArrayTypeAnalysisContext(app.SystemTypes.SystemStringType);
        var array = new LocalVariable("array", new Register(null, "array"), new SzArrayTypeAnalysisContext(app.SystemTypes.SystemObjectType));
        var klass = new LocalVariable("klass", new Register(null, "klass"));
        var element = new LocalVariable("element", new Register(null, "element"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var source = new LocalVariable("other", new Register(null, "other"));
        var allocation = kind switch
        {
            "helper" => new Instruction(0, OpCode.Call, new StringLiteral("SzArrayNew"), array, actual, new Immediate(1)),
            "parameter" => new Instruction(0, OpCode.Nop),
            "mixed" => new Instruction(0, OpCode.Phi, array, source, new Immediate(0)),
            _ => new Instruction(0, OpCode.NewArr, array, actual, new Immediate(1))
        };
        var load = new Instruction(2, OpCode.Move, element, new MemoryOperand(klass, addend: kind == "wrong_offset" ? 0x48 : 0x40));
        var call = new Instruction(3, OpCode.Call, new StringLiteral("il2cpp_vm_object_is_inst"), result, new StringLiteral("value"), element);
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Store", app.SystemTypes.SystemObjectType,
            MethodAttributes.Static | MethodAttributes.Public, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([allocation, new(1, OpCode.Move, klass, new MemoryOperand(array)), load, call, new(4, OpCode.Return, result)]),
            Locals = [array, klass, element, result, source], ParameterLocals = []
        };
        KeyFunctionRecovery.Run(method);
        Assert.That(load.Operands[1] is RuntimeClassTypeAnalysisContext, Is.EqualTo(expected));
        Assert.That(call.OpCode, Is.EqualTo(expected ? OpCode.TryCast : OpCode.Call));
        if (expected) Assert.That(call.Operands[1], Is.SameAs(app.SystemTypes.SystemStringType));
    }
}
