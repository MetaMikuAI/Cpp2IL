using System;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using FieldAttributes = AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes;
using MethodAttributes = AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes;
using TypeAttributes = AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes;

namespace Cpp2IL.Core.Tests;

public class LinqNormalizationTests
{
    [TestCase("Take", "System.Linq", "count", false)]
    [TestCase("Skip", "System.Linq", "count", false)]
    [TestCase("ElementAt", "System.Linq", "count", false)]
    [TestCase("Contains", "System.Linq", "value", false)]
    [TestCase("First", "System.Linq", "source", false)]
    [TestCase("Any", "System.Linq", "source", false)]
    [TestCase("ToArray", "System.Linq", "source", false)]
    [TestCase("Where", "Other", "predicate", true)]
    [TestCase("Where", "System.Linq", "predicate", true)]
    [TestCase("First", "System.Linq", "predicate", true)]
    public void OnlyDelegateTakingOverloadsUseCachedDelegateTypes(string name, string ns, string kind, bool expected)
    {
        var module = new ModuleDefinition("LinqNormalizationTests.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var factory = module.CorLibTypeFactory;
        var owner = new TypeDefinition("Tests", "Caller", TypeAttributes.Public);
        var enumerable = new TypeDefinition(ns, "Enumerable", TypeAttributes.Public);
        var func = new TypeDefinition("System", "Func`2", TypeAttributes.Public);
        var sequence = new TypeDefinition("System.Collections.Generic", "IEnumerable`1", TypeAttributes.Public);
        module.TopLevelTypes.Add(owner); module.TopLevelTypes.Add(enumerable);
        module.TopLevelTypes.Add(func); module.TopLevelTypes.Add(sequence);
        var generic = new GenericParameterSignature(GenericParameterType.Method, 0);
        var sourceType = new GenericInstanceTypeSignature(sequence, false, [generic]);
        var selectorType = new GenericInstanceTypeSignature(func, false, [generic, factory.Boolean]);
        var cachedType = new GenericInstanceTypeSignature(func, false, [factory.String, factory.Boolean]);
        TypeSignature lastParameter = kind switch
        {
            "count" => factory.Int32, "value" => generic, "source" => sourceType, _ => selectorType
        };
        var signature = kind == "source" ? MethodSignature.CreateStatic(factory.Object, [lastParameter])
            : MethodSignature.CreateStatic(factory.Object, [sourceType, lastParameter]);
        signature.GenericParameterCount = 1;
        var target = new MethodDefinition(name, MethodAttributes.Public | MethodAttributes.Static, signature);
        enumerable.Methods.Add(target);
        var call = new MethodSpecification(target, new GenericInstanceMethodSignature([factory.Object]));
        var cache = new FieldDefinition("<>9__0", FieldAttributes.Public | FieldAttributes.Static, new FieldSignature(cachedType));
        owner.Fields.Add(cache);
        var method = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static, MethodSignature.CreateStatic(factory.Void));
        owner.Methods.Add(method);
        var body = method.CilMethodBody = new CilMethodBody();
        var originalType = kind == "count" ? (TypeSignature)factory.Int32 : kind == "predicate" ? selectorType : factory.Object;
        var argument = new CilLocalVariable(originalType);
        body.LocalVariables.Add(argument);
        body.Instructions.Add(CilOpCodes.Ldsfld, cache);
        if (kind == "predicate") body.Instructions.Add(CilOpCodes.Stloc, argument);
        else body.Instructions.Add(CilOpCodes.Pop);
        if (kind != "source") body.Instructions.Add(CilOpCodes.Ldnull);
        body.Instructions.Add(CilOpCodes.Ldloc, argument);
        body.Instructions.Add(CilOpCodes.Call, call);
        body.Instructions.Add(CilOpCodes.Pop);
        body.Instructions.Add(CilOpCodes.Ret);
        typeof(IlGenerator).GetMethod("NormalizeLinqGenericInstantiations", BindingFlags.NonPublic | BindingFlags.Static)!.Invoke(null, [method]);
        Assert.That(argument.VariableType, Is.SameAs(expected ? cachedType : originalType));
        Assert.That(call.Signature!.TypeArguments[0], Is.SameAs(expected ? factory.String : factory.Object));
    }
}
