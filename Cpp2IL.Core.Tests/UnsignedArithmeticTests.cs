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

// ARM64 spells signed and unsigned right-shift and division as separate instructions (LSR vs ASR,
// UDIV vs SDIV), but ISIL folds each pair into one opcode. IL generation has to pick the signed or
// unsigned CIL instruction back out of the operand types, and picking wrong is silent: `shr` on a
// ushort whose high bit is set sign-extends where the original `>>` did not.
public class UnsignedArithmeticTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    private static readonly CilOpCode[] SignedOpCodes =
        [CilOpCodes.Shr, CilOpCodes.Div, CilOpCodes.Rem];

    private static readonly CilOpCode[] UnsignedOpCodes =
        [CilOpCodes.Shr_Un, CilOpCodes.Div_Un, CilOpCodes.Rem_Un];

    [TestCase(OpCode.ShiftRight, "System.UInt32", true)]
    [TestCase(OpCode.ShiftRight, "System.UInt16", true)]
    [TestCase(OpCode.ShiftRight, "System.UInt64", true)]
    [TestCase(OpCode.ShiftRight, "System.Byte", true)]
    [TestCase(OpCode.ShiftRight, "System.Int32", false)]
    [TestCase(OpCode.ShiftRight, "System.Int64", false)]
    [TestCase(OpCode.Divide, "System.UInt32", true)]
    [TestCase(OpCode.Divide, "System.Int32", false)]
    [TestCase(OpCode.Modulo, "System.UInt32", true)]
    [TestCase(OpCode.Modulo, "System.Int32", false)]
    public void OperandTypeSelectsSignedness(OpCode opCode, string typeName, bool expectUnsigned)
    {
        var il = GenerateBinaryOp(opCode, ResolveType(typeName));

        var emitted = il.Select(i => i.OpCode).ToArray();
        var expected = expectUnsigned ? UnsignedOpCodes : SignedOpCodes;
        var unexpected = expectUnsigned ? SignedOpCodes : UnsignedOpCodes;

        Assert.Multiple(() =>
        {
            Assert.That(emitted.Any(expected.Contains), Is.True,
                $"expected {(expectUnsigned ? "unsigned" : "signed")} CIL for {opCode} on {typeName}");
            Assert.That(emitted.Any(unexpected.Contains), Is.False,
                $"did not expect {(expectUnsigned ? "signed" : "unsigned")} CIL for {opCode} on {typeName}");
        });
    }

    // A shift distance is always a non-negative count, so it must not drag the operation to
    // unsigned on its own - only the value being shifted decides.
    [Test]
    public void UnsignedShiftDistanceDoesNotMakeShiftUnsigned()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var il = GenerateBinaryOp(OpCode.ShiftRight,
            appContext.SystemTypes.SystemInt32Type,
            rightType: appContext.SystemTypes.SystemUInt32Type);

        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Shr), Is.True,
            "a signed value shifted by an unsigned distance is still an arithmetic shift");
    }

    // For a divide, either operand being unsigned forces the unsigned form.
    [Test]
    public void UnsignedDivisorMakesDivideUnsigned()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var il = GenerateBinaryOp(OpCode.Divide,
            appContext.SystemTypes.SystemInt32Type,
            rightType: appContext.SystemTypes.SystemUInt32Type);

        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Div_Un), Is.True,
            "an unsigned divisor forces the unsigned divide");
    }

    // Untyped operands must keep the previous behaviour rather than guessing.
    [Test]
    public void UntypedOperandsFallBackToSigned()
    {
        var il = GenerateBinaryOp(OpCode.ShiftRight, type: null);

        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Shr), Is.True,
            "without type information the signed form is the safe default");
    }

    private static TypeAnalysisContext ResolveType(string fullName)
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var type = appContext.AssembliesByName["mscorlib"].GetTypeByFullName(fullName);

        Assert.That(type, Is.Not.Null, $"expected to find {fullName} in mscorlib");
        return type!;
    }

    private static IList<CilInstruction> GenerateBinaryOp(OpCode opCode,
        TypeAnalysisContext? type, TypeAnalysisContext? rightType = null)
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var systemObject = appContext.SystemTypes.SystemObjectType;
        var systemVoid = appContext.SystemTypes.SystemVoidType;

        var methodContext = new InjectedMethodAnalysisContext(
            systemObject,
            "BinaryOp",
            systemVoid,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            []);

        var result = new LocalVariable("result", new Register(null, "result"), type);
        var left = new LocalVariable("left", new Register(null, "left"), type);
        var right = new LocalVariable("right", new Register(null, "right"), rightType ?? type);

        var instructions = new List<Instruction>
        {
            new(0, opCode, result, left, right),
            new(1, OpCode.Return),
        };

        methodContext.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        methodContext.Locals = [result, left, right];
        methodContext.ParameterLocals = [];
        methodContext.AnalysisWarnings = [];

        var module = new ModuleDefinition("Test.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var typeDef = new TypeDefinition("Cpp2IL.Core.Tests", "UnsignedArithmeticTestType",
            TypeAttributes.Class | TypeAttributes.Public);
        module.TopLevelTypes.Add(typeDef);

        // Typed locals are emitted through ContextToTypeSignature, which needs each context to
        // carry the AsmResolver type the DLL output format would normally have attached.
        foreach (var localType in new[] { type, rightType }.OfType<TypeAnalysisContext>().Distinct())
            EnsureAsmResolverType(localType, module);

        var methodDef = new MethodDefinition("BinaryOp", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        typeDef.Methods.Add(methodDef);

        IlGenerator.GenerateIl(methodContext, methodDef);

        return methodDef.CilMethodBody!.Instructions;
    }

    private static void EnsureAsmResolverType(TypeAnalysisContext context, ModuleDefinition module)
    {
        if (context.GetExtraData<TypeDefinition>("AsmResolverType") != null)
            return;

        var placeholder = new TypeDefinition(context.Namespace, context.Name,
            TypeAttributes.Class | TypeAttributes.Public);
        module.TopLevelTypes.Add(placeholder);
        context.PutExtraData("AsmResolverType", placeholder);
    }
}
