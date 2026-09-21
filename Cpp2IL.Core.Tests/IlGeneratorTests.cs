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
    public void SignExtend_TruncatesThenWidensSignedValue(int bits)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var result = new LocalVariable("extended", new Register(null, "extended"), app.SystemTypes.SystemInt64Type);
        var instruction = new Instruction(0, OpCode.SignExtend, result, new Immediate(0xFFFFFFFF), new Immediate(bits));
        var definition = GenerateSingle(instruction, result);
        var il = definition.CilMethodBody!.Instructions;
        var narrow = bits == 8 ? CilOpCodes.Conv_I1 : bits == 16 ? CilOpCodes.Conv_I2 : CilOpCodes.Conv_I4;
        var position = il.ToList().FindIndex(i => i.OpCode == narrow);
        Assert.That(position, Is.GreaterThanOrEqualTo(0));
        Assert.That(il[position + 1].OpCode, Is.EqualTo(CilOpCodes.Conv_I8));
        Assert.That(instruction.Destination, Is.SameAs(result));
        Assert.That(instruction.SourcesAndConstants, Does.Contain(new Immediate(0xFFFFFFFF)));
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

    [TestCase(true, 0L, 1L)]
    [TestCase(true, 1L, 0L)]
    [TestCase(false, 0L, -1L)]
    [TestCase(false, 1L, -2L)]
    public void Not_ConstantFoldingPreservesBooleanVersusIntegerSemantics(bool boolean, long input, long expected)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var type = boolean ? app.SystemTypes.SystemBooleanType : app.SystemTypes.SystemInt64Type;
        var result = new LocalVariable("result", new Register(null, "result"), type);
        var not = new Instruction(0, OpCode.Not, result, new Immediate(input));
        var generated = GenerateSingle(not, result).CilMethodBody!.Instructions;
        Assert.That(generated.Any(i => i.OpCode == CilOpCodes.Ceq), Is.EqualTo(boolean));
        Assert.That(generated.Any(i => i.OpCode == CilOpCodes.Not), Is.EqualTo(!boolean));
        var cfg = new ISILControlFlowGraph([not, new(1, OpCode.Return, result)]);
        Assert.That(Cpp2IL.Core.Analysis.ConstantFolder.Run(cfg), Is.True);
        Assert.That(not.OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(((Immediate)not.Operands[1]).Value, Is.EqualTo(expected));
    }

    [TestCase(false, false)]
    [TestCase(false, true)]
    [TestCase(true, false)]
    [TestCase(true, true)]
    public void Not_UsesFieldTypeAfterInlining(bool boolean, bool isStatic)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var fieldType = boolean ? app.SystemTypes.SystemBooleanType : app.SystemTypes.SystemUInt64Type;
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), app.SystemTypes.SystemObjectType);
        var attributes = System.Reflection.FieldAttributes.Public
            | (isStatic ? System.Reflection.FieldAttributes.Static : 0);
        var field = new InjectedFieldAnalysisContext("Value", fieldType, attributes, app.SystemTypes.SystemObjectType);
        var module = new ModuleDefinition("Fields.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var owner = new TypeDefinition("Tests", "Fields", TypeAttributes.Public);
        module.TopLevelTypes.Add(owner);
        var definition = new FieldDefinition("Value", (FieldAttributes)attributes,
            new FieldSignature(boolean ? module.CorLibTypeFactory.Boolean : module.CorLibTypeFactory.UInt64));
        owner.Fields.Add(definition);
        field.PutExtraData("AsmResolverField", definition);
        var result = new LocalVariable("result", new Register(null, "result"), fieldType);
        var method = GenerateSingle(new Instruction(0, OpCode.Not, result, new FieldReference(field, receiver, 0)), result);
        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == (isStatic ? CilOpCodes.Ldsfld : CilOpCodes.Ldfld)), Is.True);
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ceq), Is.EqualTo(boolean));
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Not), Is.EqualTo(!boolean));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void Not_UsesArrayElementTypeAfterInlining(bool boolean)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var elementType = boolean ? app.SystemTypes.SystemBooleanType : app.SystemTypes.SystemUInt64Type;
        var array = new LocalVariable("array", new Register(null, "array"), new SzArrayTypeAnalysisContext(elementType));
        var result = new LocalVariable("result", new Register(null, "result"), elementType);
        var method = GenerateSingle(new Instruction(0, OpCode.Not, result, new ArrayAccess(array, new Immediate(0))), result);
        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldelem), Is.True);
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ceq), Is.EqualTo(boolean));
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Not), Is.EqualTo(!boolean));
    }

    [Test]
    public void FieldAddressArgument_EmitsLdfldaAndRetainsReceiver()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("FieldAddress.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var owner = new TypeDefinition("Tests", "Owner", TypeAttributes.Public);
        module.TopLevelTypes.Add(owner);
        var fieldDefinition = new FieldDefinition("Value", FieldAttributes.Public, new FieldSignature(module.CorLibTypeFactory.Int32));
        owner.Fields.Add(fieldDefinition);
        var field = new InjectedFieldAnalysisContext("Value", app.SystemTypes.SystemInt32Type,
            System.Reflection.FieldAttributes.Public, app.SystemTypes.SystemObjectType);
        field.PutExtraData("AsmResolverField", fieldDefinition);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"));
        var target = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Consume", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, [new ByRefTypeAnalysisContext(app.SystemTypes.SystemInt32Type)]);
        var targetDefinition = new MethodDefinition("Consume", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.Int32.MakeByReferenceType()]));
        owner.Methods.Add(targetDefinition);
        target.PutExtraData("AsmResolverMethod", targetDefinition);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, [])
        {
            Locals = [], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph([
                new Instruction(0, OpCode.CallVoid, target, new AddressOf(new FieldReference(field, receiver, 0))),
                new Instruction(1, OpCode.Return)]),
        };
        var generated = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(generated);
        IlGenerator.GenerateIl(caller, generated);
        var il = generated.CilMethodBody!.Instructions;
        Assert.That(caller.Locals, Does.Contain(receiver));
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldflda), Is.EqualTo(1));
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldfld || i.OpCode == CilOpCodes.Add), Is.False);
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Call), Is.EqualTo(1));
    }

    [TestCase(false, false)]
    [TestCase(false, true)]
    [TestCase(true, false)]
    [TestCase(true, true)]
    public void NativeShift_UsesExplicitWidthAndSignedness(bool wide, bool signed)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var type = wide ? (signed ? app.SystemTypes.SystemInt64Type : app.SystemTypes.SystemUInt64Type)
            : (signed ? app.SystemTypes.SystemInt32Type : app.SystemTypes.SystemUInt32Type);
        var result = new LocalVariable("shifted", new Register(null, "shifted"), type);
        var instruction = new Instruction(0, OpCode.ShiftRight, result, new Immediate(0x80000000L), new Immediate(31), type);
        var definition = GenerateSingle(instruction, result);
        var il = definition.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == (wide ? (signed ? CilOpCodes.Conv_I8 : CilOpCodes.Conv_U8)
            : (signed ? CilOpCodes.Conv_I4 : CilOpCodes.Conv_U4))), Is.True);
        Assert.That(il.Any(i => i.OpCode == (signed ? CilOpCodes.Shr : CilOpCodes.Shr_Un)), Is.True);
        var cfg = new ISILControlFlowGraph([instruction]);
        Assert.That(Cpp2IL.Core.Analysis.ConstantFolder.Run(cfg), Is.False);
        Assert.That(instruction.OpCode, Is.EqualTo(OpCode.ShiftRight));
    }

    [TestCase("load")]
    [TestCase("store")]
    [TestCase("address")]
    [TestCase("scratch")]
    public void NestedFieldPathsEmitEveryContainingAddressInOrder(string mode)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("NestedFields.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var intDefinition = new TypeDefinition("System", "Int32", TypeAttributes.Public);
        module.TopLevelTypes.Add(intDefinition);
        app.SystemTypes.SystemInt32Type.PutExtraData("AsmResolverType", intDefinition);
        var valueBase = module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType");
        var innerDefinition = new TypeDefinition("Tests", "Inner", TypeAttributes.Public | TypeAttributes.SequentialLayout | TypeAttributes.Sealed, valueBase);
        var outerDefinition = new TypeDefinition("Tests", "Outer", TypeAttributes.Public | TypeAttributes.SequentialLayout | TypeAttributes.Sealed, valueBase);
        var ownerDefinition = new TypeDefinition("Tests", "Owner", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(innerDefinition);
        module.TopLevelTypes.Add(outerDefinition);
        module.TopLevelTypes.Add(ownerDefinition);
        var valueType = app.AllTypes.Single(t => t.FullName == "System.ValueType");
        var inner = new InjectedTypeAnalysisContext(valueType.DeclaringAssembly, "Tests", "Inner", valueType, System.Reflection.TypeAttributes.Public);
        var outer = new InjectedTypeAnalysisContext(valueType.DeclaringAssembly, "Tests", "Outer", valueType, System.Reflection.TypeAttributes.Public);
        var owner = new InjectedTypeAnalysisContext(valueType.DeclaringAssembly, "Tests", "Owner", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        inner.PutExtraData("AsmResolverType", innerDefinition);
        outer.PutExtraData("AsmResolverType", outerDefinition);
        owner.PutExtraData("AsmResolverType", ownerDefinition);
        var contexts = new FieldAnalysisContext[]
        {
            new InjectedFieldAnalysisContext("Outer", outer, System.Reflection.FieldAttributes.Public, owner),
            new InjectedFieldAnalysisContext("Inner", inner, System.Reflection.FieldAttributes.Public, outer),
            new InjectedFieldAnalysisContext("Value", app.SystemTypes.SystemInt32Type, System.Reflection.FieldAttributes.Public, inner)
        };
        var fields = new[]
        {
            new FieldDefinition("Outer", FieldAttributes.Public, new FieldSignature(outerDefinition.ToTypeSignature(true))),
            new FieldDefinition("Inner", FieldAttributes.Public, new FieldSignature(innerDefinition.ToTypeSignature(true))),
            new FieldDefinition("Value", FieldAttributes.Public, new FieldSignature(module.CorLibTypeFactory.Int32))
        };
        ownerDefinition.Fields.Add(fields[0]);
        outerDefinition.Fields.Add(fields[1]);
        innerDefinition.Fields.Add(fields[2]);
        for (var i = 0; i < fields.Length; i++) contexts[i].PutExtraData("AsmResolverField", fields[i]);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), owner);
        var result = new LocalVariable("result", new Register(null, "result"), app.SystemTypes.SystemInt32Type);
        var reference = new FieldReference(contexts[2], receiver, 0) { ContainingFields = [contexts[0], contexts[1]] };
        var target = new InjectedMethodAnalysisContext(owner, "Consume", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, [new ByRefTypeAnalysisContext(app.SystemTypes.SystemInt32Type)]);
        var targetDefinition = new MethodDefinition("Consume", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.Int32.MakeByReferenceType()]));
        ownerDefinition.Methods.Add(targetDefinition);
        target.PutExtraData("AsmResolverMethod", targetDefinition);
        var operation = mode switch
        {
            "load" => new Instruction(0, OpCode.Move, result, reference),
            "store" => new Instruction(0, OpCode.Move, reference, new Immediate(7)),
            "scratch" => new Instruction(0, OpCode.Add, reference, new Immediate(1), new Immediate(2)),
            _ => new Instruction(0, OpCode.CallVoid, target, new AddressOf(reference))
        };
        var caller = new InjectedMethodAnalysisContext(owner, "Caller", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, [])
        {
            Locals = [receiver, result], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph([operation, new(1, OpCode.Return)])
        };
        var generated = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        ownerDefinition.Methods.Add(generated);
        IlGenerator.GenerateIl(caller, generated);
        var addresses = generated.CilMethodBody!.Instructions.Where(i => i.OpCode == CilOpCodes.Ldflda).Select(i => i.Operand).ToList();
        Assert.That(addresses, Is.EqualTo(mode == "address" ? fields : fields.Take(2)));
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
        foreach (var context in new[] { app.SystemTypes.SystemBooleanType, app.SystemTypes.SystemUInt64Type, app.SystemTypes.SystemStringType, app.SystemTypes.SystemObjectType, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemUInt32Type, app.SystemTypes.SystemInt64Type })
        {
            var placeholder = new TypeDefinition(context.Namespace, context.Name, TypeAttributes.Public);
            module.TopLevelTypes.Add(placeholder);
            context.PutExtraData("AsmResolverType", placeholder);
        }
        var type = new TypeDefinition("Tests", "Recovery", TypeAttributes.Public);
        module.TopLevelTypes.Add(type);
        var definition = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(result.Type!.FullName switch
            {
                "System.Boolean" => module.CorLibTypeFactory.Boolean,
                "System.String" => module.CorLibTypeFactory.String,
                "System.Int32" => module.CorLibTypeFactory.Int32,
                "System.UInt32" => module.CorLibTypeFactory.UInt32,
                "System.Int64" => module.CorLibTypeFactory.Int64,
                _ => module.CorLibTypeFactory.UInt64
            }));
        type.Methods.Add(definition);
        IlGenerator.GenerateIl(caller, definition);
        return definition;
    }
}
