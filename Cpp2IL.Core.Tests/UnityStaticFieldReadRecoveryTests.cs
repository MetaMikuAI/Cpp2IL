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
    [TestCase("Vector2", "componentRead")]
    [TestCase("Vector3", "componentRead")]
    [TestCase("Quaternion", "componentRead")]
    [TestCase("Vector3", "componentWrite")]
    [TestCase("Vector3", "componentAddress")]
    [TestCase("Vector3", "componentSelf")]
    [TestCase("Vector3", "componentUnknown")]
    [TestCase("Vector3", "componentWrongType")]
    public void UnityConstant_OnlyRecoverWholeStaticRead(string type, string operation)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var component = operation.StartsWith("component");
        var read = operation is "read" or "componentRead";
        var write = operation is "write" or "componentWrite";
        var address = operation is "address" or "componentAddress";
        var self = operation is "self" or "componentSelf";
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
        var member = new InjectedFieldAnalysisContext(operation == "componentUnknown" ? "other" : type == "Quaternion" ? "w" : "x",
            operation == "componentWrongType" ? app.SystemTypes.SystemInt32Type : app.SystemTypes.SystemSingleType,
            System.Reflection.FieldAttributes.Public, owner);
        var target = component ? member : field;
        var result = new LocalVariable("result", new Register(null, "result"),
            address ? new ByRefTypeAnalysisContext(target.FieldType) : target.FieldType);
        var access = new FieldReference(target, receiver, 0, component ? field : null);
        var move = write ? new Instruction(0, OpCode.Move, access, result)
            : new Instruction(0, OpCode.Move, result, address ? new AddressOf(access) : access);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
        {
            Locals = [receiver, result], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph([move, new Instruction(1, OpCode.Return)]),
        };
        var module = new ModuleDefinition("UnityStaticRead.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        foreach (var context in new[] { owner, app.SystemTypes.SystemObjectType, app.SystemTypes.SystemSingleType, app.SystemTypes.SystemInt32Type })
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
        var memberDefinition = new FieldDefinition(member.Name, FieldAttributes.Public, new FieldSignature(member.FieldType.ToTypeSignature()));
        ownerDefinition.Fields.Add(memberDefinition);
        member.PutExtraData("AsmResolverField", memberDefinition);
        var getterDefinition = new MethodDefinition(getter.Name, MethodAttributes.Public | MethodAttributes.Static, MethodSignature.CreateStatic(getter.ReturnType.ToTypeSignature()));
        ownerDefinition.Methods.Add(getterDefinition);
        getter.PutExtraData("AsmResolverMethod", getterDefinition);
        var generated = self ? getterDefinition : new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static, MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        if (!self)
            ownerDefinition.Methods.Add(generated);

        IlGenerator.GenerateIl(caller, generated);

        var il = generated.CilMethodBody!.Instructions;
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Call), Is.EqualTo(read ? 1 : 0));
        if (read)
        {
            Assert.That(((IMethodDescriptor)il.Single(i => i.OpCode == CilOpCodes.Call).Operand!).Name!.Value, Is.EqualTo(getter.Name));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldloc || i.OpCode == CilOpCodes.Ldsfld || i.OpCode == CilOpCodes.Ldsflda), Is.False, "static getter needs no receiver");
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldloca), Is.EqualTo(component ? 1 : 0));
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldfld), Is.EqualTo(component ? 1 : 0));
        }
        else
            Assert.That(il.Any(i => i.OpCode == (write ? component ? CilOpCodes.Stfld : CilOpCodes.Stsfld
                : address ? component ? CilOpCodes.Ldflda : CilOpCodes.Ldsflda : component ? CilOpCodes.Ldfld : CilOpCodes.Ldsfld)), Is.True);
    }
}
