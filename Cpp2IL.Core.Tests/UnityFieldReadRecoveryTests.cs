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

public class UnityFieldReadRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    [TestCase("read")]
    [TestCase("write")]
    [TestCase("address")]
    [TestCase("self")]
    [TestCase("wrongReturn")]
    [TestCase("foreign")]
    public void Button_OnlyRecoverProvenGetterRead(string operation)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        // The stripped fixture has no UGUI. Mirror the installed package's exact member shape.
        var assembly = new InjectedAssemblyAnalysisContext("UnityEngine.UI", app);
        var owner = new InjectedTypeAnalysisContext(assembly, "UnityEngine.UI", "Button", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var eventType = new InjectedTypeAnalysisContext(assembly, "", "ButtonClickedEvent", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.NestedPublic) { DeclaringType = owner };
        var field = new InjectedFieldAnalysisContext("m_OnClick", eventType, System.Reflection.FieldAttributes.Private, owner);
        var getter = new InjectedMethodAnalysisContext(owner, "get_onClick", eventType, System.Reflection.MethodAttributes.Public, []);
        owner.Properties.Add(new InjectedPropertyAnalysisContext("onClick", eventType, getter, null, System.Reflection.PropertyAttributes.None, owner));
        if (operation == "foreign")
        {
            owner = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly, owner.Namespace, owner.Name, owner.BaseType, owner.Attributes);
            field = new InjectedFieldAnalysisContext(field.Name, field.FieldType, field.Attributes, owner);
        }
        if (operation == "wrongReturn")
            getter.OverrideReturnType = app.SystemTypes.SystemObjectType;
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), owner);
        var result = new LocalVariable("result", new Register(null, "result"),
            operation == "address" ? new ByRefTypeAnalysisContext(field.FieldType) : field.FieldType);
        var access = new FieldReference(field, receiver, field.Offset);
        var move = operation == "write" ? new Instruction(0, OpCode.Move, access, result)
            : new Instruction(0, OpCode.Move, result, operation == "address" ? new AddressOf(access) : access);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
        {
            Locals = [receiver, result], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph([move, new Instruction(1, OpCode.Return)]),
        };
        var module = new ModuleDefinition("UnityRead.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        foreach (var context in new[] { owner, field.FieldType, app.SystemTypes.SystemObjectType })
        {
            var definition = new TypeDefinition(context.Namespace, context.Name, TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
            module.TopLevelTypes.Add(definition);
            context.PutExtraData("AsmResolverType", definition);
        }
        var ownerDefinition = owner.GetExtraData<TypeDefinition>("AsmResolverType")!;
        var fieldDefinition = new FieldDefinition(field.Name, FieldAttributes.Private, new FieldSignature(field.FieldType.ToTypeSignature()));
        ownerDefinition.Fields.Add(fieldDefinition);
        field.PutExtraData("AsmResolverField", fieldDefinition);
        var getterDefinition = new MethodDefinition(getter.Name, MethodAttributes.Public, MethodSignature.CreateInstance(getter.ReturnType.ToTypeSignature()));
        ownerDefinition.Methods.Add(getterDefinition);
        getter.PutExtraData("AsmResolverMethod", getterDefinition);
        var generated = operation == "self" ? getterDefinition : new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static, MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        if (operation != "self")
            ownerDefinition.Methods.Add(generated);

        IlGenerator.GenerateIl(caller, generated);

        var il = generated.CilMethodBody!.Instructions;
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Callvirt), Is.EqualTo(operation == "read" ? 1 : 0), "callvirt preserves null receiver behavior");
        if (operation == "read")
            Assert.That(((IMethodDescriptor)il.Single(i => i.OpCode == CilOpCodes.Callvirt).Operand!).Name!.Value, Is.EqualTo("get_onClick"));
        else
            Assert.That(il.Any(i => i.OpCode == (operation == "write" ? CilOpCodes.Stfld : operation == "address" ? CilOpCodes.Ldflda : CilOpCodes.Ldfld)), Is.True);
    }
}
