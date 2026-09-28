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

public class PrimitiveFieldReadRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    [TestCase("System.Int32", "read")]
    [TestCase("System.Int64", "read")]
    [TestCase("System.Single", "read")]
    [TestCase("System.Double", "read")]
    [TestCase("System.Boolean", "read")]
    [TestCase("System.Int32", "byref")]
    [TestCase("System.Int32", "write")]
    [TestCase("System.Int32", "address")]
    public void PrimitiveField_OnlyReadWholeValue(string typeName, string operation)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = app.AllTypes.Single(t => t.FullName == typeName);
        var field = owner.Fields.Single(f => f.Name == "m_value");
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"),
            operation == "byref" ? new ByRefTypeAnalysisContext(owner) : owner);
        var result = new LocalVariable("result", new Register(null, "result"),
            operation == "address" ? new ByRefTypeAnalysisContext(owner) : owner);
        var access = new FieldReference(field, receiver, field.Offset);
        var move = operation == "write" ? new Instruction(0, OpCode.Move, access, result)
            : new Instruction(0, OpCode.Move, result, operation == "address" ? new AddressOf(access) : access);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
        {
            Locals = [receiver, result], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph([move, new Instruction(1, OpCode.Return)]),
        };
        var module = new ModuleDefinition("PrimitiveRead.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var definition = new TypeDefinition(owner.Namespace, owner.Name, TypeAttributes.Public,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(definition);
        owner.PutExtraData("AsmResolverType", definition);
        var fieldDefinition = new FieldDefinition(field.Name, FieldAttributes.Private, new FieldSignature(owner.ToTypeSignature()));
        definition.Fields.Add(fieldDefinition);
        field.PutExtraData("AsmResolverField", fieldDefinition);
        var generated = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static, MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        definition.Methods.Add(generated);

        IlGenerator.GenerateIl(caller, generated);

        var il = generated.CilMethodBody!.Instructions;
        var read = operation is "read" or "byref";
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldobj), Is.EqualTo(read ? 1 : 0));
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldfld), Is.False);
        if (read)
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldloca), Is.EqualTo(operation != "byref"));
        else
            Assert.That(il.Any(i => i.OpCode == (operation == "write" ? CilOpCodes.Stfld : CilOpCodes.Ldflda)), Is.True);
    }

    [TestCase("foreign")]
    [TestCase("compound")]
    [TestCase("wrongType")]
    public void UnprovenField_IsNotRecovered(string kind)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var original = app.SystemTypes.SystemInt32Type;
        var owner = new InjectedTypeAnalysisContext(kind == "foreign" ? app.Assemblies.First(a => a.Name != "mscorlib") : original.DeclaringAssembly,
            "System", "Int32", original.BaseType, original.Attributes);
        var field = new InjectedFieldAnalysisContext("m_value", kind == "wrongType" ? app.SystemTypes.SystemSingleType : owner,
            System.Reflection.FieldAttributes.Private, owner);
        owner.Fields.Add(field);
        if (kind == "compound")
            owner.Fields.Add(new InjectedFieldAnalysisContext("other", owner, System.Reflection.FieldAttributes.Private, owner));
        Assert.That(PrimitiveFieldReadRecovery.IsWholeValueRead(field), Is.False);
    }
}
