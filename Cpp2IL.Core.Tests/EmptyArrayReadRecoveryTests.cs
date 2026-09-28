using System;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;

namespace Cpp2IL.Core.Tests;

public class EmptyArrayReadRecoveryTests
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
    [TestCase("mutable")]
    [TestCase("wrongReturn")]
    [TestCase("foreign")]
    public void EmptyArray_OnlyRecoverProvenStaticRead(string operation)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = app.AllTypes.Single(t => t.FullName == "System.EmptyArray`1");
        var field = owner.Fields.Single(f => f.Name == "Value");
        var array = owner.DeclaringAssembly.GetTypeByFullName("System.Array")!;
        var factory = array.Methods.Single(m => m.Name == "Empty");
        if (operation == "foreign")
        {
            owner = new InjectedTypeAnalysisContext(app.Assemblies.First(a => a.Name != "mscorlib"), owner.Namespace, owner.Name, owner.BaseType, owner.Attributes);
            field = new InjectedFieldAnalysisContext(field.Name, field.FieldType, field.Attributes, owner);
        }
        if (operation == "mutable")
            field.Attributes &= ~System.Reflection.FieldAttributes.InitOnly;
        if (operation == "wrongReturn")
            factory.OverrideReturnType = app.SystemTypes.SystemObjectType;
        var instance = new GenericInstanceTypeAnalysisContext(owner, [app.SystemTypes.SystemInt32Type]);
        var concrete = new ConcreteGenericFieldAnalysisContext(field, instance);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), instance);
        var result = new LocalVariable("result", new Register(null, "result"),
            operation == "address" ? new ByRefTypeAnalysisContext(concrete.FieldType) : concrete.FieldType);
        var access = new FieldReference(concrete, receiver, 0);
        var move = operation == "write" ? new Instruction(0, OpCode.Move, access, result)
            : new Instruction(0, OpCode.Move, result, operation == "address" ? new AddressOf(access) : access);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
        {
            Locals = [receiver, result], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph([move, new Instruction(1, OpCode.Return)]),
        };
        var module = new ModuleDefinition("EmptyRead.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        foreach (var context in new[] { owner, array, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemObjectType })
        {
            var definition = new TypeDefinition(context.Namespace, context.Name, TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
            module.TopLevelTypes.Add(definition);
            context.PutExtraData("AsmResolverType", definition);
        }
        var ownerDefinition = owner.GetExtraData<TypeDefinition>("AsmResolverType")!;
        ownerDefinition.GenericParameters.Add(new GenericParameter("T"));
        var fieldDefinition = new FieldDefinition(field.Name, FieldAttributes.Public | FieldAttributes.Static | FieldAttributes.InitOnly, new FieldSignature(field.FieldType.ToTypeSignature()));
        ownerDefinition.Fields.Add(fieldDefinition);
        field.PutExtraData("AsmResolverField", fieldDefinition);
        var factoryDefinition = new MethodDefinition("Empty", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(factory.ReturnType.ToTypeSignature()));
        factoryDefinition.GenericParameters.Add(new GenericParameter("T"));
        factoryDefinition.Signature!.GenericParameterCount = 1;
        array.GetExtraData<TypeDefinition>("AsmResolverType")!.Methods.Add(factoryDefinition);
        factory.PutExtraData("AsmResolverMethod", factoryDefinition);
        var generated = operation == "self" ? factoryDefinition : new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static, MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        if (operation != "self")
            ownerDefinition.Methods.Add(generated);

        IlGenerator.GenerateIl(caller, generated);

        var il = generated.CilMethodBody!.Instructions;
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Call), Is.EqualTo(operation == "read" ? 1 : 0));
        if (operation == "read")
        {
            var call = (MethodSpecification)il.Single(i => i.OpCode == CilOpCodes.Call).Operand!;
            Assert.That(call.Signature!.TypeArguments.Single().FullName, Is.EqualTo("System.Int32"));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldsfld), Is.False);
        }
        else
            Assert.That(il.Any(i => i.OpCode == (operation == "write" ? CilOpCodes.Stsfld : operation == "address" ? CilOpCodes.Ldsflda : CilOpCodes.Ldsfld)), Is.True);
    }
}
