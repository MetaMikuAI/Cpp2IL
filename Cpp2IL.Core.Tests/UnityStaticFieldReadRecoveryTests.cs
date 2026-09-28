using System;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;

namespace Cpp2IL.Core.Tests;

public class UnityStaticFieldReadRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    [TestCase("Vector2", "read")]
    [TestCase("Vector3", "read")]
    [TestCase("Quaternion", "read")]
    [TestCase("Vector3", "write")]
    [TestCase("Vector3", "address")]
    [TestCase("Vector3", "self")]
    [TestCase("Vector3", "mutable")]
    [TestCase("Vector3", "wrongReturn")]
    [TestCase("Vector3", "foreign")]
    [TestCase("Vector3", "unknown")]
    public void UnityConstant_OnlyRecoverWholeStaticRead(string type, string operation)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var assembly = new InjectedAssemblyAnalysisContext(operation == "foreign" ? "Game" : "UnityEngine.CoreModule", app);
        var owner = new InjectedTypeAnalysisContext(assembly, "UnityEngine", type, app.SystemTypes.SystemInt32Type.BaseType, System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Sealed);
        var property = type == "Quaternion" ? "identity" : "zero";
        var fieldName = type == "Quaternion" ? "identityQuaternion" : "zeroVector";
        var field = new InjectedFieldAnalysisContext(operation == "unknown" ? "unknown" : fieldName, owner,
            System.Reflection.FieldAttributes.Private | System.Reflection.FieldAttributes.Static | (operation == "mutable" ? 0 : System.Reflection.FieldAttributes.InitOnly), owner);
        var getter = new InjectedMethodAnalysisContext(owner, "get_" + property,
            operation == "wrongReturn" ? app.SystemTypes.SystemObjectType : owner,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, []);
        owner.Properties.Add(new InjectedPropertyAnalysisContext(property, owner, getter, null, System.Reflection.PropertyAttributes.None, owner));
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), owner);
        var result = new LocalVariable("result", new Register(null, "result"),
            operation == "address" ? new ByRefTypeAnalysisContext(owner) : owner);
        var access = new FieldReference(field, receiver, 0);
        var move = operation == "write" ? new Instruction(0, OpCode.Move, access, result)
            : new Instruction(0, OpCode.Move, result, operation == "address" ? new AddressOf(access) : access);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
        {
            Locals = [receiver, result], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph([move, new Instruction(1, OpCode.Return)]),
        };
        var module = new ModuleDefinition("UnityStaticRead.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        foreach (var context in new[] { owner, app.SystemTypes.SystemObjectType })
        {
            var definition = new TypeDefinition(context.Namespace, context.Name, TypeAttributes.Public,
                context.IsValueType ? module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType") : module.CorLibTypeFactory.Object.Type);
            module.TopLevelTypes.Add(definition);
            context.PutExtraData("AsmResolverType", definition);
        }
        var ownerDefinition = owner.GetExtraData<TypeDefinition>("AsmResolverType")!;
        var fieldDefinition = new FieldDefinition(field.Name, FieldAttributes.Private | FieldAttributes.Static, new FieldSignature(owner.ToTypeSignature()));
        ownerDefinition.Fields.Add(fieldDefinition);
        field.PutExtraData("AsmResolverField", fieldDefinition);
        var getterDefinition = new MethodDefinition(getter.Name, MethodAttributes.Public | MethodAttributes.Static, MethodSignature.CreateStatic(getter.ReturnType.ToTypeSignature()));
        ownerDefinition.Methods.Add(getterDefinition);
        getter.PutExtraData("AsmResolverMethod", getterDefinition);
        var generated = operation == "self" ? getterDefinition : new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static, MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        if (operation != "self")
            ownerDefinition.Methods.Add(generated);

        IlGenerator.GenerateIl(caller, generated);

        var il = generated.CilMethodBody!.Instructions;
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Call), Is.EqualTo(operation == "read" ? 1 : 0));
        if (operation == "read")
        {
            Assert.That(((IMethodDescriptor)il.Single(i => i.OpCode == CilOpCodes.Call).Operand!).Name!.Value, Is.EqualTo(getter.Name));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldloc || i.OpCode == CilOpCodes.Ldloca || i.OpCode == CilOpCodes.Ldsfld), Is.False, "static getter needs no receiver");
        }
        else
            Assert.That(il.Any(i => i.OpCode == (operation == "write" ? CilOpCodes.Stsfld : operation == "address" ? CilOpCodes.Ldsflda : CilOpCodes.Ldsfld)), Is.True);
    }
}
