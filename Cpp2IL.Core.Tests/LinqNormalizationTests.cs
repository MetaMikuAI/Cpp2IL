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
    [TestCase("single", true)]
    [TestCase("multiple", false)]
    [TestCase("address", false)]
    [TestCase("different", false)]
    [TestCase("mistyped", true)]
    [TestCase("nested", false)]
    [TestCase("nearby", true)]
    [TestCase("copy", true)]
    [TestCase("unknown", false)]
    [TestCase("cycle", false)]
    [TestCase("selectorAddress", false)]
    [TestCase("constructed", true)]
    [TestCase("indexed", true)]
    [TestCase("nestedMatch", true)]
    public void RecoveredReturnTypeUpdatesOnlyMatchingSingleAssignmentResults(string usage, bool expected)
    {
        var module = new ModuleDefinition("LinqResultTests.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var factory = module.CorLibTypeFactory;
        var owner = new TypeDefinition("Tests", "Caller", TypeAttributes.Public);
        var enumerable = new TypeDefinition("System.Linq", "Enumerable", TypeAttributes.Public);
        var func = new TypeDefinition("System", usage == "indexed" ? "Func`3" : "Func`2", TypeAttributes.Public);
        var sequence = new TypeDefinition("System.Collections.Generic", "IEnumerable`1", TypeAttributes.Public);
        module.TopLevelTypes.Add(owner); module.TopLevelTypes.Add(enumerable);
        module.TopLevelTypes.Add(func); module.TopLevelTypes.Add(sequence);
        var input = new GenericParameterSignature(GenericParameterType.Method, 0);
        var output = new GenericParameterSignature(GenericParameterType.Method, 1);
        var sourceType = new GenericInstanceTypeSignature(sequence, false, [input]);
        var returnType = new GenericInstanceTypeSignature(sequence, false, [output]);
        TypeSignature selectorResult = usage is "nested" or "nestedMatch" ? returnType : output;
        var selectorType = new GenericInstanceTypeSignature(func, false, usage == "indexed"
            ? [input, factory.Int32, selectorResult] : [input, selectorResult]);
        TypeSignature actualResult = usage == "nestedMatch" ? new GenericInstanceTypeSignature(sequence, false, [factory.String]) : factory.String;
        var cachedType = new GenericInstanceTypeSignature(func, false, usage == "indexed"
            ? [factory.Int32, factory.Int32, actualResult] : [factory.Int32, actualResult]);
        var signature = MethodSignature.CreateStatic(returnType, [sourceType, selectorType]);
        signature.GenericParameterCount = 2;
        var target = new MethodDefinition("Select", MethodAttributes.Public | MethodAttributes.Static, signature);
        enumerable.Methods.Add(target);
        var call = new MethodSpecification(target, new GenericInstanceMethodSignature([factory.Object, factory.Object]));
        var cache = new FieldDefinition("<>9__0", FieldAttributes.Public | FieldAttributes.Static, new FieldSignature(cachedType));
        owner.Fields.Add(cache);
        var method = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static, MethodSignature.CreateStatic(factory.Void));
        owner.Methods.Add(method);
        var body = method.CilMethodBody = new CilMethodBody();
        var selector = new CilLocalVariable(usage == "mistyped"
            ? new GenericInstanceTypeSignature(func, false, [factory.Int32, factory.Boolean]) : cachedType);
        var originalType = new GenericInstanceTypeSignature(sequence, false, [usage == "different" ? factory.Boolean : factory.Object]);
        var result = new CilLocalVariable(originalType);
        body.LocalVariables.Add(selector); body.LocalVariables.Add(result);
        body.Instructions.Add(CilOpCodes.Ldsfld, cache);
        body.Instructions.Add(CilOpCodes.Stloc, selector);
        if (usage is "unknown" or "cycle")
        {
            if (usage == "cycle") body.Instructions.Add(CilOpCodes.Ldloc, selector);
            else body.Instructions.Add(CilOpCodes.Ldnull);
            body.Instructions.Add(CilOpCodes.Stloc, selector);
        }
        if (usage == "selectorAddress")
        {
            body.Instructions.Add(CilOpCodes.Ldloca, selector);
            body.Instructions.Add(CilOpCodes.Pop);
        }
        if (usage == "constructed")
        {
            var ctor = new MemberReference(new TypeSpecification(cachedType), ".ctor",
                MethodSignature.CreateInstance(factory.Void, [factory.Object, factory.IntPtr]));
            body.Instructions.Add(CilOpCodes.Ldnull);
            body.Instructions.Add(CilOpCodes.Ldc_I4_0);
            body.Instructions.Add(CilOpCodes.Conv_I);
            body.Instructions.Add(CilOpCodes.Newobj, ctor);
            body.Instructions.Add(CilOpCodes.Stloc, selector);
        }
        if (usage == "copy")
        {
            var copy = new CilLocalVariable(cachedType);
            body.LocalVariables.Add(copy);
            body.Instructions.Add(CilOpCodes.Ldloc, selector);
            body.Instructions.Add(CilOpCodes.Stloc, copy);
            selector = copy;
        }
        if (usage == "nearby")
        {
            var unrelated = new FieldDefinition("<>9__1", FieldAttributes.Public | FieldAttributes.Static,
                new FieldSignature(new GenericInstanceTypeSignature(func, false, [factory.Int32, factory.Boolean])));
            owner.Fields.Add(unrelated);
            body.Instructions.Add(CilOpCodes.Ldsfld, unrelated);
            body.Instructions.Add(CilOpCodes.Pop);
        }
        body.Instructions.Add(CilOpCodes.Ldnull);
        body.Instructions.Add(CilOpCodes.Ldloc, selector);
        body.Instructions.Add(CilOpCodes.Call, call);
        body.Instructions.Add(CilOpCodes.Stloc, result);
        if (usage == "multiple")
        {
            body.Instructions.Add(CilOpCodes.Ldnull);
            body.Instructions.Add(CilOpCodes.Stloc, result);
        }
        if (usage == "address")
        {
            body.Instructions.Add(CilOpCodes.Ldloca, result);
            body.Instructions.Add(CilOpCodes.Pop);
        }
        body.Instructions.Add(CilOpCodes.Ret);
        typeof(IlGenerator).GetMethod("NormalizeLinqGenericInstantiations", BindingFlags.NonPublic | BindingFlags.Static)!.Invoke(null, [method]);
        var expectedType = expected ? new GenericInstanceTypeSignature(sequence, false, [factory.String]) : originalType;
        Assert.That(SignatureComparer.Default.Equals(result.VariableType, expectedType), Is.True);
        Assert.That(call.Signature!.TypeArguments[1], Is.SameAs(usage == "nested" ? factory.Object : factory.String));
    }

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
