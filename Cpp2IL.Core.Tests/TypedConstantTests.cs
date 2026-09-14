using System;
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

public class TypedConstantTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [TestCase("Int64", 0L)]
    [TestCase("Int64", 1L)]
    [TestCase("Int64", -1L)]
    [TestCase("Int64", long.MinValue)]
    [TestCase("UInt64", 0L)]
    [TestCase("UInt64", -1L)]
    public void WideReturnUsesI8EvenForSmallConstants(string type, long value)
    {
        var load = GenerateReturn(type, value);
        Assert.That(load.OpCode, Is.EqualTo(CilOpCodes.Ldc_I8));
        Assert.That(load.Operand, Is.EqualTo(value));
    }

    [TestCase("Int32", 2147483648L, int.MinValue)]
    [TestCase("Int32", 4294967295L, -1)]
    [TestCase("UInt32", 4294967295L, -1)]
    [TestCase("UInt32", 0L, 0)]
    [TestCase("Int32", -1L, -1)]
    public void WordConstantsPreserveTheir32BitPattern(string type, long value, int expected)
    {
        var load = GenerateReturn(type, value);
        Assert.That(load.OpCode, Is.EqualTo(CilOpCodes.Ldc_I4));
        Assert.That(load.Operand, Is.EqualTo(expected));
    }

    [TestCase("Single")]
    [TestCase("Double")]
    public void FloatingZeroUsesFloatingStackType(string type)
    {
        var load = GenerateReturn(type, 0);
        Assert.That(load.OpCode, Is.EqualTo(type == "Single" ? CilOpCodes.Ldc_R4 : CilOpCodes.Ldc_R8));
        Assert.That(Convert.ToDouble(load.Operand), Is.EqualTo(0d));
    }

    [Test]
    public void ReferenceZeroStillUsesNull()
    {
        Assert.That(GenerateReturn("Object", 0).OpCode, Is.EqualTo(CilOpCodes.Ldnull));
    }

    [Test]
    public void DoesNotTruncateBeyondAWordOrGuessNonzeroFloatBits()
    {
        Assert.That(GenerateReturn("Int32", 4294967296L).OpCode, Is.EqualTo(CilOpCodes.Ldc_I8));
        Assert.That(GenerateReturn("Single", 1).OpCode, Is.EqualTo(CilOpCodes.Ldc_I4));
    }

    private static CilInstruction GenerateReturn(string type, long value)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var returnType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System." + type)!;
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Constant",
            returnType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([new Instruction(0, OpCode.Return, new Immediate(value))]);
        context.Locals = [];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];
        var module = new ModuleDefinition("TypedConstantTests.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var owner = new TypeDefinition("Tests", "Constants", TypeAttributes.Public);
        module.TopLevelTypes.Add(owner);
        var factory = module.CorLibTypeFactory;
        var signature = type switch
        {
            "Int64" => factory.Int64, "UInt64" => factory.UInt64,
            "Int32" => factory.Int32, "UInt32" => factory.UInt32,
            "Single" => factory.Single, "Double" => factory.Double,
            _ => factory.Object
        };
        var method = new MethodDefinition("Constant", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(signature));
        owner.Methods.Add(method);
        IlGenerator.GenerateIl(context, method);
        return method.CilMethodBody!.Instructions.First(i => i.OpCode != CilOpCodes.Nop);
    }
}
