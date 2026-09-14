using System;
using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using ReflectionMethodAttributes = System.Reflection.MethodAttributes;

namespace Cpp2IL.Core.Tests;

public class IlGeneratorTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [Test]
    public void StaticCall_DoesNotLoadMethodInfoOperand()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var systemObject = appContext.SystemTypes.SystemObjectType;
        var systemVoid = appContext.SystemTypes.SystemVoidType;
        var systemInt = appContext.SystemTypes.SystemInt32Type;

        var callerContext = new InjectedMethodAnalysisContext(
            systemObject,
            "Caller",
            systemVoid,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            []);

        var targetContext = new InjectedMethodAnalysisContext(
            systemObject,
            "TargetStatic",
            systemVoid,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            [systemInt, systemInt]);

        var x = new LocalVariable("x", new Register(null, "x"));
        var y = new LocalVariable("y", new Register(null, "y"));

        var instructions = new List<Instruction>
        {
            
            new(0, OpCode.Move, x, Imm(5)),
            new(1, OpCode.Move, y, Imm(10)),
            // Operand layout: target, arg0, arg1, trailing-non-parameter.
            new(2, OpCode.CallVoid, targetContext, x, y, Imm(999)),
            new(3, OpCode.Return),
        };

        callerContext.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        callerContext.Locals = [x, y];
        callerContext.ParameterLocals = [];
        callerContext.AnalysisWarnings = [];

        var module = new ModuleDefinition("Test.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var typeDef = new TypeDefinition("Cpp2IL.Core.Tests", "IlGeneratorTestType", TypeAttributes.Class | TypeAttributes.Public);
        module.TopLevelTypes.Add(typeDef);

        var callerMethodDef = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        typeDef.Methods.Add(callerMethodDef);

        var targetMethodDef = new MethodDefinition("TargetStatic", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,
                [module.CorLibTypeFactory.Int32, module.CorLibTypeFactory.Int32]));
        typeDef.Methods.Add(targetMethodDef);
        targetContext.PutExtraData("AsmResolverMethod", targetMethodDef);

        IlGenerator.GenerateIl(callerContext, callerMethodDef);

        var il = callerMethodDef.CilMethodBody!.Instructions;

        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call), Is.True, "expected generated method to contain a call");
        Assert.That(il.Any(i => i.Operand is int intOperand && intOperand == 999), Is.False,
            "trailing non-parameter operand must not be emitted as a call argument");
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldloc), Is.EqualTo(2),
            "expected exactly two Ldloc instructions for the two parameters of the target method");
    }

    [TestCase(8)]
    [TestCase(16)]
    [TestCase(32)]
    public void ZeroExtend_Emits64BitMask(int bits)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var result = new LocalVariable("extended", new Register(null, "extended"), app.SystemTypes.SystemUInt64Type);
        var definition = GenerateSingle(new Instruction(0, OpCode.ZeroExtend, result, new Immediate(-1), new Immediate(bits)), result);
        var il = definition.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Conv_U8), Is.True);
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_I8 && Equals(i.Operand, (1L << bits) - 1)), Is.True);
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.And), Is.True);
    }

    [Test]
    public void IsInstance_EmitsManagedTypeTest()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var result = new LocalVariable("matches", new Register(null, "matches"), app.SystemTypes.SystemBooleanType);
        var definition = GenerateSingle(new Instruction(0, OpCode.IsInstance, result, app.SystemTypes.SystemStringType, new StringLiteral("test")), result);
        var il = definition.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Isinst), Is.True);
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.True);
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Cgt_Un), Is.True);
    }

    [TestCase(false)]
    [TestCase(true)]
    public void TryCast_EmitsReferenceResultRatherThanBoolean(bool nullObject)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var result = new LocalVariable("cast", new Register(null, "cast"), app.SystemTypes.SystemStringType);
        IOperand value = nullObject ? new Immediate(0) : new StringLiteral("test");
        var definition = GenerateSingle(new Instruction(0, OpCode.TryCast, result, app.SystemTypes.SystemStringType, value), result);
        var il = definition.CilMethodBody!.Instructions;
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Isinst), Is.EqualTo(1));
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Cgt_Un || i.OpCode == CilOpCodes.Castclass), Is.False);
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.EqualTo(nullObject));
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_I4_0), Is.False);
    }

    private static MethodDefinition GenerateSingle(Instruction instruction, LocalVariable result)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", result.Type!,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([instruction, new Instruction(1, OpCode.Return, result)]),
            Locals = [result], ParameterLocals = [], AnalysisWarnings = []
        };
        var module = new ModuleDefinition("Test.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        foreach (var context in new[] { app.SystemTypes.SystemBooleanType, app.SystemTypes.SystemUInt64Type, app.SystemTypes.SystemStringType })
        {
            var placeholder = new TypeDefinition(context.Namespace, context.Name, TypeAttributes.Public);
            module.TopLevelTypes.Add(placeholder);
            context.PutExtraData("AsmResolverType", placeholder);
        }
        var type = new TypeDefinition("Tests", "Recovery", TypeAttributes.Public);
        module.TopLevelTypes.Add(type);
        var definition = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(instruction.OpCode == OpCode.IsInstance ? module.CorLibTypeFactory.Boolean : instruction.OpCode == OpCode.TryCast ? module.CorLibTypeFactory.String : module.CorLibTypeFactory.UInt64));
        type.Methods.Add(definition);
        IlGenerator.GenerateIl(caller, definition);
        return definition;
    }
}