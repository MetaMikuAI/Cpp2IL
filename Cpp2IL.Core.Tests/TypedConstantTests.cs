using System;
using System.Linq;
using ReflectionBindingFlags = System.Reflection.BindingFlags;
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

    [TestCase(OpCode.CheckEqual, "Object", 0L, false, true)]
    [TestCase(OpCode.CheckNotEqual, "Object", 0L, true, true)]
    [TestCase(OpCode.CheckEqual, "String", 0L, true, true)]
    [TestCase(OpCode.CheckEqual, "Int32", 0L, false, false)]
    [TestCase(OpCode.CheckEqual, "IntPtr", 0L, false, false)]
    [TestCase(OpCode.CheckEqual, "Object", 1L, false, false)]
    [TestCase(OpCode.CheckGreater, "Object", 0L, false, false)]
    [TestCase(OpCode.And, "Object", 0L, false, false)]
    [TestCase(OpCode.CheckEqual, "Pointer", 0L, false, false)]
    [TestCase(OpCode.CheckEqual, "ByRef", 0L, false, false)]
    [TestCase(OpCode.CheckEqual, "Generic", 0L, false, false)]
    public void ReferenceEqualityRecognizesManagedReferenceNullChecks(OpCode opcode, string typeName,
        long value, bool literalLeft, bool expected)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var type = typeName switch
        {
            "Pointer" => new PointerTypeAnalysisContext(app.SystemTypes.SystemInt32Type),
            "ByRef" => new ByRefTypeAnalysisContext(app.SystemTypes.SystemObjectType),
            "Generic" => new GenericParameterTypeAnalysisContext("T", 0,
                LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_VAR,
                System.Reflection.GenericParameterAttributes.None, app.SystemTypes.SystemObjectType),
            _ => app.AssembliesByName["mscorlib"].GetTypeByFullName("System." + typeName)!
        };
        var source = new LocalVariable("source", new Register(null, "source"), type);
        var result = new LocalVariable("result", new Register(null, "result"), app.SystemTypes.SystemBooleanType);
        var literal = new Immediate(value);
        var instruction = new Instruction(0, opcode, result, literalLeft ? literal : source, literalLeft ? source : literal);
        var helper = typeof(IlGenerator).GetMethod("ReferenceEqualityType", ReflectionBindingFlags.NonPublic | ReflectionBindingFlags.Static)!;
        var actual = helper.Invoke(null, [instruction]);
        Assert.That(actual, Is.SameAs(expected ? type : null));
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

    [TestCase(OpCode.Add, "Int64", "Int64", 1L, false, true)]
    [TestCase(OpCode.Subtract, "UInt64", "UInt64", 1L, true, true)]
    [TestCase(OpCode.And, "Int64", "Int64", 255L, false, true)]
    [TestCase(OpCode.And, "Int32", "Int32", 2147483648L, false, false)]
    [TestCase(OpCode.Or, "UInt32", "UInt32", 4294967295L, true, false)]
    [TestCase(OpCode.CheckEqual, "Int64", "Boolean", 0L, false, true)]
    [TestCase(OpCode.CheckEqual, "UInt32", "Boolean", 4294967295L, false, false)]
    [TestCase(OpCode.CheckLess, "UInt32", "Boolean", 4294967295L, false, true)]
    [TestCase(OpCode.CheckGreater, "UInt64", "Boolean", 1L, false, false)]
    [TestCase(OpCode.ShiftRight, "Int64", "Int64", 1L, false, false)]
    [TestCase(OpCode.And, "Int32", "Object", 4294967295L, false, true)]
    [TestCase(OpCode.And, "Int32", "Int64", 4294967295L, false, true)]
    [TestCase(OpCode.And, "Object", "Int32", 4294967295L, false, true)]
    [TestCase(OpCode.And, "Int32", "Int32", 4294967296L, false, true)]
    public void BinaryConstantsUseOnlyProvenIntegerWidths(OpCode opcode, string sourceName, string resultName,
        long value, bool literalLeft, bool wide)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        TypeAnalysisContext Type(string name) => app.AssembliesByName["mscorlib"].GetTypeByFullName("System." + name)!;
        var source = new LocalVariable("source", new Register(null, "source"), Type(sourceName));
        var result = new LocalVariable("result", new Register(null, "result"), Type(resultName));
        var literal = new Immediate(value);
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "BinaryConstant",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([
                new Instruction(0, opcode, result, literalLeft ? literal : source, literalLeft ? source : literal),
                new Instruction(1, OpCode.Return)]),
            Locals = [source, result], ParameterLocals = [], AnalysisWarnings = []
        };
        var module = new ModuleDefinition("BinaryConstantTests.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var owner = new TypeDefinition("Tests", "BinaryConstants", TypeAttributes.Public);
        module.TopLevelTypes.Add(owner);
        foreach (var type in new[] { source.Type!, result.Type! }.Distinct())
            if (type.GetExtraData<TypeDefinition>("AsmResolverType") == null)
            {
                var placeholder = new TypeDefinition(type.Namespace, type.Name, TypeAttributes.Public);
                module.TopLevelTypes.Add(placeholder);
                type.PutExtraData("AsmResolverType", placeholder);
            }
        var method = new MethodDefinition("BinaryConstant", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(method);
        IlGenerator.GenerateIl(context, method);
        var load = method.CilMethodBody!.Instructions.First(i => i.OpCode == CilOpCodes.Ldc_I4 || i.OpCode == CilOpCodes.Ldc_I8);
        Assert.That(load.OpCode, Is.EqualTo(wide ? CilOpCodes.Ldc_I8 : CilOpCodes.Ldc_I4));
        Assert.That(Convert.ToInt64(load.Operand), Is.EqualTo(wide ? value : unchecked((int)value)));
    }
}
