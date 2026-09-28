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
    [TestCase("System.Collections.Generic.KeyValuePair`2", "key", "Key")]
    [TestCase("System.Collections.Generic.KeyValuePair`2", "value", "Value")]
    [TestCase("System.Collections.Generic.Dictionary`2+Enumerator", "_current", "Current")]
    [TestCase("System.Collections.Generic.Dictionary`2+KeyCollection+Enumerator", "_currentKey", "Current")]
    [TestCase("System.Collections.Generic.Dictionary`2+ValueCollection+Enumerator", "_currentValue", "Current")]
    [TestCase("System.Collections.Generic.Queue`1", "_size", "Count")]
    [TestCase("System.Collections.Generic.Stack`1", "_size", "Count")]
    [TestCase("System.Collections.Generic.HashSet`1", "_count", "Count")]
    [TestCase("System.Collections.Generic.HashSet`1+Enumerator", "_current", "Current")]
    public void FrameworkGetter_BindsActualMetadata(string typeName, string fieldName, string propertyName)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        TypeAnalysisContext owner;
        if (typeName is "System.Collections.Generic.Queue`1" or "System.Collections.Generic.Stack`1")
        {
            // These types are stripped from the fixture; use their verified Mono member shape.
            owner = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly, "System.Collections.Generic", typeName.Split('.').Last(), app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
            owner.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0, LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_VAR, System.Reflection.GenericParameterAttributes.None, owner));
            owner.Fields.Add(new InjectedFieldAnalysisContext(fieldName, app.SystemTypes.SystemInt32Type, System.Reflection.FieldAttributes.Private, owner));
            var injectedGetter = new InjectedMethodAnalysisContext(owner, "get_Count", app.SystemTypes.SystemInt32Type, System.Reflection.MethodAttributes.Public, []);
            owner.Properties.Add(new InjectedPropertyAnalysisContext("Count", app.SystemTypes.SystemInt32Type, injectedGetter, null, System.Reflection.PropertyAttributes.None, owner));
        }
        else
            owner = app.AllTypes.Single(t => t.FullName == typeName);
        var arguments = owner.GenericParameters.Select(_ => (TypeAnalysisContext)app.SystemTypes.SystemInt32Type).ToArray();
        var instance = new GenericInstanceTypeAnalysisContext(owner, arguments);
        var field = new ConcreteGenericFieldAnalysisContext(owner.Fields.Single(f => f.Name == fieldName), instance);
        var getter = Cpp2IL.Core.Analysis.CollectionFieldReadRecovery.TryGetGetter(field, new MethodDefinition("Caller", MethodAttributes.Static, null));

        Assert.That(getter, Is.TypeOf<ConcreteGenericMethodAnalysisContext>());
        Assert.That(getter!.Name, Is.EqualTo("get_" + propertyName));
        Assert.That(getter.ReturnType.FullName, Is.EqualTo(field.FieldType.FullName));
        Assert.That(((ConcreteGenericMethodAnalysisContext)getter).TypeGenericParameters, Is.EqualTo(arguments));
    }

    [Test]
    public void NullableValue_ReadsThroughGetValueOrDefault()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = app.AllTypes.Single(t => t.FullName == "System.Nullable`1");
        var instance = new GenericInstanceTypeAnalysisContext(owner, [app.SystemTypes.SystemInt32Type]);
        var field = new ConcreteGenericFieldAnalysisContext(owner.Fields.Single(f => f.Name == "value"), instance);
        var getter = Cpp2IL.Core.Analysis.CollectionFieldReadRecovery.TryGetGetter(field, new MethodDefinition("Caller", MethodAttributes.Static, null));

        Assert.That(getter, Is.TypeOf<ConcreteGenericMethodAnalysisContext>());
        Assert.That(getter!.Name, Is.EqualTo("GetValueOrDefault"));
        Assert.That(getter.Parameters, Is.Empty);
    }

    [Test]
    public void DictionaryCurrent_DifferentGenericArguments_IsNotRecovered()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = app.AllTypes.Single(t => t.FullName == "System.Collections.Generic.Dictionary`2+Enumerator");
        var getter = owner.Properties.Single(p => p.Name == "Current").Getter!;
        var returnType = (GenericInstanceTypeAnalysisContext)getter.ReturnType;
        var wrongArguments = returnType.GenericArguments.ToArray();
        wrongArguments[0] = app.SystemTypes.SystemStringType;
        getter.OverrideReturnType = new GenericInstanceTypeAnalysisContext(returnType.GenericType, wrongArguments);
        var field = new ConcreteGenericFieldAnalysisContext(owner.Fields.Single(f => f.Name == "_current"),
            new GenericInstanceTypeAnalysisContext(owner, [app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemInt32Type]));
        Assert.That(Cpp2IL.Core.Analysis.CollectionFieldReadRecovery.TryGetGetter(field, new MethodDefinition("Caller", MethodAttributes.Static, null)), Is.Null);
    }

    [Test]
    public void HashSet_SameAssemblyNameWithoutIdentity_IsNotRecovered()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var other = new InjectedAssemblyAnalysisContext("System.Core", app);
        var owner = new InjectedTypeAnalysisContext(other, "System.Collections.Generic", "HashSet`1", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var field = new InjectedFieldAnalysisContext("_count", app.SystemTypes.SystemInt32Type, System.Reflection.FieldAttributes.Private, owner);
        Assert.That(Cpp2IL.Core.Analysis.CollectionFieldReadRecovery.TryGetGetter(field, new MethodDefinition("Caller", MethodAttributes.Static, null)), Is.Null);
    }

    [TestCase(false, "read")]
    [TestCase(false, "write")]
    [TestCase(false, "address")]
    [TestCase(true, "read")]
    [TestCase(true, "write")]
    [TestCase(true, "address")]
    public void StringAndNullable_OnlyReadTheirPureProperty(bool nullable, string operation)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = nullable ? app.AllTypes.Single(t => t.FullName == "System.Nullable`1") : app.SystemTypes.SystemStringType;
        var field = owner.Fields.Single(f => f.Name == (nullable ? "hasValue" : "_stringLength"));
        var getter = owner.Properties.Single(p => p.Name == (nullable ? "HasValue" : "Length")).Getter!;
        TypeAnalysisContext receiverType = nullable ? new GenericInstanceTypeAnalysisContext(owner, [app.SystemTypes.SystemInt32Type]) : owner;
        FieldAnalysisContext referenced = nullable ? new ConcreteGenericFieldAnalysisContext(field, (GenericInstanceTypeAnalysisContext)receiverType) : field;
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), receiverType);
        var access = new FieldReference(referenced, receiver, field.Offset);
        var result = new LocalVariable("result", new Register(null, "result"),
            operation == "address" ? new ByRefTypeAnalysisContext(field.FieldType) : field.FieldType);
        var move = operation == "write" ? new Instruction(0, OpCode.Move, access, new Immediate(1))
            : new Instruction(0, OpCode.Move, result, operation == "address" ? new AddressOf(access) : access);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
        {
            Locals = [receiver, result], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph([move, new Instruction(1, OpCode.Return)]),
        };
        var module = new ModuleDefinition("PureRead.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        foreach (var context in new[] { owner, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemBooleanType }.Distinct())
        {
            var definition = new TypeDefinition(context.Namespace, context.Name, TypeAttributes.Public,
                context.IsValueType ? module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType") : module.CorLibTypeFactory.Object.Type);
            module.TopLevelTypes.Add(definition);
            context.PutExtraData("AsmResolverType", definition);
        }
        var ownerDefinition = owner.GetExtraData<TypeDefinition>("AsmResolverType")!;
        if (nullable)
            ownerDefinition.GenericParameters.Add(new GenericParameter("T"));
        var fieldDefinition = new FieldDefinition(field.Name, FieldAttributes.Private, new FieldSignature(field.FieldType.ToTypeSignature()));
        ownerDefinition.Fields.Add(fieldDefinition);
        field.PutExtraData("AsmResolverField", fieldDefinition);
        var getterDefinition = new MethodDefinition(getter.Name, MethodAttributes.Public, MethodSignature.CreateInstance(getter.ReturnType.ToTypeSignature()));
        ownerDefinition.Methods.Add(getterDefinition);
        getter.PutExtraData("AsmResolverMethod", getterDefinition);
        var generated = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static, MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        ownerDefinition.Methods.Add(generated);

        IlGenerator.GenerateIl(caller, generated);

        var il = generated.CilMethodBody!.Instructions;
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Call || i.OpCode == CilOpCodes.Callvirt), Is.EqualTo(operation == "read" ? 1 : 0));
        if (operation == "read")
        {
            var call = il.Single(i => i.OpCode == CilOpCodes.Call || i.OpCode == CilOpCodes.Callvirt);
            Assert.That(call.OpCode, Is.EqualTo(nullable ? CilOpCodes.Call : CilOpCodes.Callvirt));
            Assert.That(((IMethodDescriptor)call.Operand!).Name!.Value, Is.EqualTo(getter.Name));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldloca), Is.EqualTo(nullable));
        }
        else
            Assert.That(il.Any(i => i.OpCode == (operation == "write" ? CilOpCodes.Stfld : CilOpCodes.Ldflda)), Is.True);
    }

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
