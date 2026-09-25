using System;
using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
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

    [TestCase("value")]
    [TestCase("ref")]
    [TestCase("receiver")]
    [TestCase("mismatch")]
    public void NativeAggregateAddress_RespectsManagedCallSignature(string kind)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var aggregate = app.AllTypes.Single(t => t.FullName == "UnityEngine.Bounds");
        var module = new ModuleDefinition("AggregateCall.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var type = new TypeDefinition("Tests", "Aggregate", TypeAttributes.Public | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(type);
        aggregate.PutExtraData("AsmResolverType", type);
        var value = new LocalVariable("value", new Register(null, "value"), aggregate);
        var parameterType = kind == "ref" ? new ByRefTypeAnalysisContext(aggregate)
            : kind == "mismatch" ? app.SystemTypes.SystemInt32Type : aggregate;
        var isStatic = kind != "receiver";
        var target = new InjectedMethodAnalysisContext(aggregate, "Consume", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | (isStatic ? ReflectionMethodAttributes.Static : 0),
            isStatic ? [parameterType] : []);
        var signature = kind == "ref" ? type.ToTypeSignature(true).MakeByReferenceType()
            : kind == "mismatch" ? module.CorLibTypeFactory.Int32 : type.ToTypeSignature(true);
        var targetDefinition = new MethodDefinition("Consume", MethodAttributes.Public | (isStatic ? MethodAttributes.Static : 0),
            isStatic ? MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [signature])
                : MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        type.Methods.Add(targetDefinition);
        target.PutExtraData("AsmResolverMethod", targetDefinition);
        var caller = new InjectedMethodAnalysisContext(aggregate, "Caller", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, [])
        {
            Locals = [value], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph([
                new Instruction(0, OpCode.CallVoid, target, new AddressOf(value)),
                new Instruction(1, OpCode.Return)])
        };
        var generated = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(generated);
        IlGenerator.GenerateIl(caller, generated);
        var il = generated.CilMethodBody!.Instructions;
        var call = il.ToList().FindIndex(i => i.OpCode == CilOpCodes.Call);
        Assert.That(call, Is.GreaterThan(0));
        Assert.That(il[call - 1].OpCode, Is.EqualTo(kind == "value" ? CilOpCodes.Ldloc : CilOpCodes.Ldloca));
        Assert.That(il[call - 1].Operand, Is.SameAs(generated.CilMethodBody.LocalVariables[0]));
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

    [TestCase("load", false)]
    [TestCase("store", false)]
    [TestCase("address", false)]
    [TestCase("scratch", false)]
    [TestCase("load", true)]
    [TestCase("store", true)]
    [TestCase("address", true)]
    [TestCase("scratch", true)]
    [TestCase("load", true, true, false)]
    [TestCase("store", true, true, false)]
    [TestCase("address", true, true, false)]
    [TestCase("scratch", true, true, false)]
    [TestCase("load", true, true, true)]
    [TestCase("store", true, true, true)]
    [TestCase("address", true, true, true)]
    [TestCase("scratch", true, true, true)]
    public void NestedFieldPathsEmitEveryContainingAddressInOrder(string mode, bool valueReceiver,
        bool parameterReceiver = false, bool byRefReceiver = false)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("NestedFields.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var intDefinition = new TypeDefinition("System", "Int32", TypeAttributes.Public);
        module.TopLevelTypes.Add(intDefinition);
        app.SystemTypes.SystemInt32Type.PutExtraData("AsmResolverType", intDefinition);
        var valueBase = module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType");
        var innerDefinition = new TypeDefinition("Tests", "Inner", TypeAttributes.Public | TypeAttributes.SequentialLayout | TypeAttributes.Sealed, valueBase);
        var outerDefinition = new TypeDefinition("Tests", "Outer", TypeAttributes.Public | TypeAttributes.SequentialLayout | TypeAttributes.Sealed, valueBase);
        var ownerDefinition = new TypeDefinition("Tests", "Owner", TypeAttributes.Public,
            valueReceiver ? valueBase : module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(innerDefinition);
        module.TopLevelTypes.Add(outerDefinition);
        module.TopLevelTypes.Add(ownerDefinition);
        var valueType = app.AllTypes.Single(t => t.FullName == "System.ValueType");
        var inner = new InjectedTypeAnalysisContext(valueType.DeclaringAssembly, "Tests", "Inner", valueType, System.Reflection.TypeAttributes.Public);
        var outer = new InjectedTypeAnalysisContext(valueType.DeclaringAssembly, "Tests", "Outer", valueType, System.Reflection.TypeAttributes.Public);
        var owner = new InjectedTypeAnalysisContext(valueType.DeclaringAssembly, "Tests", "Owner",
            valueReceiver ? valueType : app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
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
        TypeAnalysisContext receiverType = byRefReceiver ? new ByRefTypeAnalysisContext(owner) : owner;
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), receiverType);
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
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, parameterReceiver ? [receiverType] : [])
        {
            Locals = parameterReceiver ? [result] : [receiver, result], ParameterLocals = parameterReceiver ? [receiver] : [],
            ControlFlowGraph = new ISILControlFlowGraph([operation, new(1, OpCode.Return)])
        };
        var generated = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, parameterReceiver
                ? [byRefReceiver ? ownerDefinition.ToTypeSignature(true).MakeByReferenceType() : ownerDefinition.ToTypeSignature(true)] : []));
        if (parameterReceiver)
            generated.ParameterDefinitions.Add(new ParameterDefinition(1, "receiver", (ParameterAttributes)0));
        ownerDefinition.Methods.Add(generated);
        IlGenerator.GenerateIl(caller, generated);
        var addresses = generated.CilMethodBody!.Instructions.Where(i => i.OpCode == CilOpCodes.Ldflda).Select(i => i.Operand).ToList();
        Assert.That(addresses, Is.EqualTo(mode == "address" ? fields : fields.Take(2)));
        var firstAddress = generated.CilMethodBody.Instructions.First(i => i.OpCode == CilOpCodes.Ldflda);
        var receiverLoad = generated.CilMethodBody.Instructions[generated.CilMethodBody.Instructions.IndexOf(firstAddress) - 1];
        Assert.That(receiverLoad.OpCode, Is.EqualTo(parameterReceiver
            ? (byRefReceiver ? CilOpCodes.Ldarg : CilOpCodes.Ldarga)
            : (valueReceiver ? CilOpCodes.Ldloca : CilOpCodes.Ldloc)));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void NativeUnsignedComparisonsExecuteAtTheirDeclaredWidth(bool wide)
    {
        var types = Cpp2IlApi.CurrentAppContext!.SystemTypes;
        long[] values = [0, 1, -1, int.MinValue, int.MaxValue, 0x100000000L, long.MinValue, long.MaxValue];
        foreach (var operation in new[] { OpCode.CheckLess, OpCode.CheckGreater, OpCode.CheckLessOrEqual, OpCode.CheckGreaterOrEqual })
        foreach (var left in values)
        foreach (var right in values)
        {
            var result = new LocalVariable("result", new Register(null, "result"), types.SystemBooleanType);
            var instruction = new Instruction(0, operation, result, new Immediate(left), new Immediate(right),
                wide ? types.SystemUInt64Type : types.SystemUInt32Type);
            var generated = GenerateSingle(instruction, result);
            var a = wide ? unchecked((ulong)left) : unchecked((uint)left);
            var b = wide ? unchecked((ulong)right) : unchecked((uint)right);
            var expected = operation switch
            {
                OpCode.CheckLess => a < b, OpCode.CheckGreater => a > b,
                OpCode.CheckLessOrEqual => a <= b, _ => a >= b
            };
            Assert.That(ExecuteBoolean(generated), Is.EqualTo(expected), $"{operation} {left}, {right}; wide={wide}");
        }
    }

    // Execute the generated primitive CIL itself, including its conversions and local stores.
    private static bool ExecuteBoolean(MethodDefinition definition)
    {
        var method = new System.Reflection.Emit.DynamicMethod("Compare", typeof(bool), []);
        var emitter = method.GetILGenerator();
        var body = definition.CilMethodBody!;
        var locals = body.LocalVariables.Select(_ => emitter.DeclareLocal(typeof(bool))).ToArray();
        var opcodes = typeof(System.Reflection.Emit.OpCodes).GetFields()
            .Where(f => f.FieldType == typeof(System.Reflection.Emit.OpCode))
            .Select(f => (System.Reflection.Emit.OpCode)f.GetValue(null)!).ToDictionary(o => o.Name!);
        var labels = body.Instructions.ToDictionary(i => i, _ => emitter.DefineLabel(), (IEqualityComparer<CilInstruction>)ReferenceEqualityComparer.Instance);
        foreach (var instruction in body.Instructions)
        {
            emitter.MarkLabel(labels[instruction]);
            var opcode = opcodes[instruction.OpCode.Mnemonic];
            switch (instruction.Operand)
            {
                case null: emitter.Emit(opcode); break;
                case long value: emitter.Emit(opcode, value); break;
                case int value: emitter.Emit(opcode, value); break;
                case AsmResolver.DotNet.Code.Cil.CilLocalVariable local: emitter.Emit(opcode, locals[local.Index]); break;
                case CilInstructionLabel label: emitter.Emit(opcode, labels[label.Instruction!]); break;
                default: throw new InvalidOperationException($"Unexpected primitive CIL: {instruction}");
            }
        }
        return method.CreateDelegate<Func<bool>>()();
    }

    [Test]
    public void UnresolvedMemoryStore_IsReportedRatherThanDropped()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var value = new LocalVariable("value", new Register(null, "value"), app.SystemTypes.SystemInt32Type);
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"), app.SystemTypes.SystemInt64Type);
        var store = new Instruction(0, OpCode.Move, new MemoryOperand(pointer, addend: 8, accessSize: 4), value);
        var il = GenerateSingle(store, value).CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr && i.Operand is string s && s.StartsWith("Unmanaged memory store: ")), Is.True);
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

    [TestCase(false, 24, true)]
    [TestCase(true, 24, true)]
    [TestCase(false, 8, false)]
    [TestCase(false, 0, false)]
    public void ZeroStoreToEmbeddedValueTypeField_InitializesOnlyAWholeAggregate(bool isStatic, int accessSize, bool whole)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var aggregate = app.AllTypes.Single(t => t.FullName == "UnityEngine.Bounds");
        var module = new ModuleDefinition("ZeroField.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var aggregateDefinition = new TypeDefinition("Tests", "Aggregate", TypeAttributes.Public | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(aggregateDefinition);
        aggregate.PutExtraData("AsmResolverType", aggregateDefinition);
        var owner = new TypeDefinition("Tests", "Owner", TypeAttributes.Public);
        module.TopLevelTypes.Add(owner);
        var fieldDefinition = new FieldDefinition("Bounds", FieldAttributes.Public | (isStatic ? FieldAttributes.Static : 0),
            new FieldSignature(aggregateDefinition.ToTypeSignature(true)));
        owner.Fields.Add(fieldDefinition);
        var field = new InjectedFieldAnalysisContext("Bounds", aggregate,
            System.Reflection.FieldAttributes.Public | (isStatic ? System.Reflection.FieldAttributes.Static : 0), app.SystemTypes.SystemObjectType);
        field.PutExtraData("AsmResolverField", fieldDefinition);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"));
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, [])
        {
            Locals = [receiver], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph([
                new Instruction(0, OpCode.Move, new FieldReference(field, receiver, 0) { AccessSize = accessSize }, Imm(0)),
                new Instruction(1, OpCode.Return)]),
        };
        var generated = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(generated);
        IlGenerator.GenerateIl(caller, generated);
        var il = generated.CilMethodBody!.Instructions;
        // UnityEngine.Bounds is 24 bytes; a narrower store keeps its (mismatched) scalar form.
        Assert.That(il.Count(i => i.OpCode == (isStatic ? CilOpCodes.Ldsflda : CilOpCodes.Ldflda)), Is.EqualTo(whole ? 1 : 0));
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Initobj), Is.EqualTo(whole ? 1 : 0));
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld || i.OpCode == CilOpCodes.Stsfld || i.OpCode == CilOpCodes.Ldc_I4), Is.EqualTo(!whole));
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldloc), Is.EqualTo(isStatic ? 0 : 1));
    }

    [TestCase("packed", true)]
    [TestCase("wide", false)]
    [TestCase("enum", false)]
    public void ZeroRegisterArgument_IsDefaultOnlyForSingleRegisterAggregates(string kind, bool expectDefault)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var parameterType = kind switch
        {
            "wide" => app.AllTypes.Single(t => t.FullName == "UnityEngine.Bounds"),
            "enum" => app.AllTypes.First(t => t.IsEnumType && t.EnumUnderlyingType == app.SystemTypes.SystemInt32Type),
            _ => app.AllTypes.First(t => t is { Type: LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE, IsEnumType: false }
                && t.GenericParameters.Count == 0 && Utils.TypeSizes.UnboxedSize(t, 8) == 8
                && t.Fields.Count(f => !f.IsStatic) == 2),
        };
        var module = new ModuleDefinition("ZeroArgument.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var parameterDefinition = new TypeDefinition("Tests", "Parameter", TypeAttributes.Public | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", kind == "enum" ? "Enum" : "ValueType"));
        module.TopLevelTypes.Add(parameterDefinition);
        parameterType.PutExtraData("AsmResolverType", parameterDefinition);
        var owner = new TypeDefinition("Tests", "Owner", TypeAttributes.Public);
        module.TopLevelTypes.Add(owner);
        var target = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Consume", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, [parameterType]);
        var targetDefinition = new MethodDefinition("Consume", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [parameterDefinition.ToTypeSignature(true)]));
        owner.Methods.Add(targetDefinition);
        target.PutExtraData("AsmResolverMethod", targetDefinition);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, [])
        {
            Locals = [], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph([
                new Instruction(0, OpCode.CallVoid, target, Imm(0)),
                new Instruction(1, OpCode.Return)]),
        };
        var generated = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(generated);
        IlGenerator.GenerateIl(caller, generated);
        var il = generated.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Initobj), Is.EqualTo(expectDefault));
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_I4), Is.EqualTo(!expectDefault));
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Call), Is.EqualTo(1));
    }
}
