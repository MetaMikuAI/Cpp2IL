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
    [TestCase("System.Int64", "write")]
    [TestCase("System.Single", "write")]
    [TestCase("System.Double", "write")]
    [TestCase("System.Boolean", "write")]
    [TestCase("System.Int32", "writeByref")]
    [TestCase("System.Int32", "writeNested")]
    [TestCase("System.Int32", "writeComputed")]
    [TestCase("System.Int32", "address")]
    [TestCase("System.Int32", "offsetWrite")]
    [TestCase("System.Int32", "offsetAddress")]
    public void PrimitiveField_RecoversWholeValueAccess(string typeName, string operation)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = app.AllTypes.Single(t => t.FullName == typeName);
        var field = owner.Fields.Single(f => f.Name == "m_value");
        Assert.That(field.Offset, Is.Zero, "metadata offsets are relative to the unboxed primitive");
        var invalidOffset = operation.StartsWith("offset");
        var write = operation is "write" or "writeByref" or "writeNested" or "writeComputed" or "offsetWrite";
        var address = operation is "address" or "offsetAddress";
        var byref = operation is "byref" or "writeByref";
        if (invalidOffset)
            field.Offset = 4;
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"),
            byref ? new ByRefTypeAnalysisContext(owner) : operation == "writeNested" ? app.SystemTypes.SystemObjectType : owner);
        var result = new LocalVariable("result", new Register(null, "result"),
            address ? new ByRefTypeAnalysisContext(owner) : owner);
        var access = new FieldReference(field, receiver, field.Offset);
        var move = operation == "writeComputed" ? new Instruction(0, OpCode.Add, access, result, new Immediate(1))
            : write ? new Instruction(0, OpCode.Move, access, result)
            : new Instruction(0, OpCode.Move, result, address ? new AddressOf(access) : access);
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
        if (operation == "writeNested")
        {
            var holder = new TypeDefinition("Test", "Holder", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
            module.TopLevelTypes.Add(holder);
            app.SystemTypes.SystemObjectType.PutExtraData("AsmResolverType", holder);
            var containing = new InjectedFieldAnalysisContext("number", owner, System.Reflection.FieldAttributes.Public, app.SystemTypes.SystemObjectType);
            var containingDefinition = new FieldDefinition("number", FieldAttributes.Public, new FieldSignature(owner.ToTypeSignature()));
            holder.Fields.Add(containingDefinition);
            containing.PutExtraData("AsmResolverField", containingDefinition);
            access.ContainingField = containing;
        }
        var generated = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static, MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        definition.Methods.Add(generated);

        IlGenerator.GenerateIl(caller, generated);

        var il = generated.CilMethodBody!.Instructions;
        var read = operation is "read" or "byref";
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldobj), Is.EqualTo(read ? 1 : 0));
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldfld), Is.False);
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Stobj), Is.EqualTo(write && !invalidOffset ? 1 : 0));
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Stfld), Is.EqualTo(operation == "offsetWrite" ? 1 : 0));
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldflda), Is.EqualTo(operation is "writeNested" or "offsetAddress" ? 1 : 0));
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldloca), Is.EqualTo(!byref && operation != "writeNested"));
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
            System.Reflection.FieldAttributes.Private, owner) { Offset = 0 };
        owner.Fields.Add(field);
        if (kind == "compound")
            owner.Fields.Add(new InjectedFieldAnalysisContext("other", owner, System.Reflection.FieldAttributes.Private, owner));
        Assert.That(PrimitiveFieldReadRecovery.IsWholeValueField(field), Is.False);
    }
}
