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

public class CollectionFieldReadRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    [TestCase(false, "read")]
    [TestCase(true, "read")]
    [TestCase(true, "byref")]
    [TestCase(false, "write")]
    [TestCase(true, "write")]
    [TestCase(false, "address")]
    [TestCase(true, "address")]
    [TestCase(false, "foreign")]
    [TestCase(true, "foreign")]
    [TestCase(false, "self")]
    [TestCase(true, "self")]
    [TestCase(false, "wrongReturn")]
    [TestCase(true, "wrongReturn")]
    public void CollectionField_OnlyReadsUseMatchingPublicGetter(bool enumerator, string operation)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = app.AllTypes.Single(t => t.FullName == (enumerator
            ? "System.Collections.Generic.List`1+Enumerator" : "System.Collections.Generic.List`1"));
        var field = owner.Fields.Single(f => f.Name == (enumerator ? "_current" : "_size"));
        var getter = owner.Properties.Single(p => p.Name == (enumerator ? "Current" : "Count")).Getter!;
        if (operation == "foreign")
        {
            var other = new InjectedTypeAnalysisContext(app.Assemblies.First(a => a.Name != "mscorlib"),
                owner.Namespace, owner.Name, owner.BaseType, owner.Attributes) { DeclaringType = owner.DeclaringType };
            other.GenericParameters.AddRange(owner.GenericParameters);
            field = new InjectedFieldAnalysisContext(field.Name, field.FieldType, field.Attributes, other);
            owner = other;
        }
        if (operation == "wrongReturn")
            getter.OverrideReturnType = app.SystemTypes.SystemObjectType;
        var instance = new GenericInstanceTypeAnalysisContext(owner, [app.SystemTypes.SystemInt32Type]);
        var concrete = new ConcreteGenericFieldAnalysisContext(field, instance);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"),
            operation == "byref" ? new ByRefTypeAnalysisContext(instance) : instance);
        var access = new FieldReference(concrete, receiver, concrete.Offset);
        var result = new LocalVariable("result", new Register(null, "result"),
            operation == "address" ? new ByRefTypeAnalysisContext(app.SystemTypes.SystemInt32Type) : app.SystemTypes.SystemInt32Type);
        var instruction = operation == "write" ? new Instruction(0, OpCode.Move, access, new Immediate(1))
            : new Instruction(0, OpCode.Move, result, operation == "address" ? new AddressOf(access) : access);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
        {
            Locals = [receiver, result], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph([instruction, new Instruction(1, OpCode.Return)]),
        };
        var module = new ModuleDefinition("CollectionRead.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        foreach (var context in new[] { app.SystemTypes.SystemObjectType, app.SystemTypes.SystemInt32Type, owner })
        {
            var definition = new TypeDefinition(context.Namespace, context.Name, TypeAttributes.Public,
                context.IsValueType ? module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType") : module.CorLibTypeFactory.Object.Type);
            module.TopLevelTypes.Add(definition);
            context.PutExtraData("AsmResolverType", definition);
        }
        var ownerDefinition = owner.GetExtraData<TypeDefinition>("AsmResolverType")!;
        ownerDefinition.GenericParameters.Add(new GenericParameter("T"));
        var fieldDefinition = new FieldDefinition(field.Name, FieldAttributes.Private, new FieldSignature(field.FieldType.ToTypeSignature()));
        ownerDefinition.Fields.Add(fieldDefinition);
        field.PutExtraData("AsmResolverField", fieldDefinition);
        var getterDefinition = new MethodDefinition(getter.Name, MethodAttributes.Public,
            MethodSignature.CreateInstance(getter.ReturnType.ToTypeSignature()));
        ownerDefinition.Methods.Add(getterDefinition);
        getter.PutExtraData("AsmResolverMethod", getterDefinition);
        var generated = operation == "self" ? getterDefinition : new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        if (operation != "self")
            ownerDefinition.Methods.Add(generated);

        IlGenerator.GenerateIl(caller, generated);

        var il = generated.CilMethodBody!.Instructions;
        var replace = operation is "read" or "byref";
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Call || i.OpCode == CilOpCodes.Callvirt), Is.EqualTo(replace ? 1 : 0));
        if (replace)
        {
            var call = il.Single(i => i.OpCode == CilOpCodes.Call || i.OpCode == CilOpCodes.Callvirt);
            Assert.That(call.OpCode, Is.EqualTo(enumerator ? CilOpCodes.Call : CilOpCodes.Callvirt), "reference reads retain null checks");
            var signature = ((IMethodDescriptor)call.Operand!).DeclaringType!.ToTypeSignature(null);
            Assert.That(signature, Is.TypeOf<GenericInstanceTypeSignature>());
            Assert.That(((GenericInstanceTypeSignature)signature).TypeArguments[0].FullName, Is.EqualTo("System.Int32"));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldloca), Is.EqualTo(enumerator && operation != "byref"));
        }
        else
            Assert.That(il.Any(i => i.OpCode == (operation == "write" ? CilOpCodes.Stfld : operation == "address" ? CilOpCodes.Ldflda : CilOpCodes.Ldfld)), Is.True);
    }
}
