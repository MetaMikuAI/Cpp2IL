using System;
using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;

namespace Cpp2IL.Core.Tests.Analysis;

public class ValueArgumentTests
{
    [TestCase("local", false)]
    [TestCase("field", false)]
    [TestCase("array", false)]
    [TestCase("local", true)]
    [TestCase("field", true)]
    [TestCase("array", true)]
    [TestCase("this", false)]
    [TestCase("mismatch", false)]
    [TestCase("constructor", false)]
    [TestCase("constructor", true)]
    public void LoadsValueOnlyForMatchingByValueParameter(string storage, bool byRef)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var valueType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Decimal")!;
        var module = new ModuleDefinition("ValueArgument.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var host = new TypeDefinition("Tests", "Host", TypeAttributes.Public);
        var valueDefinition = new TypeDefinition("System", "Decimal", TypeAttributes.Public | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(host);
        module.TopLevelTypes.Add(valueDefinition);
        valueType.PutExtraData("AsmResolverType", valueDefinition);
        app.SystemTypes.SystemObjectType.PutExtraData("AsmResolverType", host);
        var parameter = byRef ? new ByRefTypeAnalysisContext(valueType)
            : storage == "mismatch" ? app.SystemTypes.SystemInt32Type : valueType;
        var signatureType = byRef ? valueDefinition.ToTypeSignature().MakeByReferenceType()
            : storage == "mismatch" ? module.CorLibTypeFactory.Int32 : valueDefinition.ToTypeSignature();
        var local = new LocalVariable("value", new Register(null, "value"), valueType);
        var locals = new List<LocalVariable> { local };
        IOperand location = local;
        if (storage == "field")
        {
            var field = new InjectedFieldAnalysisContext("Value", valueType, System.Reflection.FieldAttributes.Public, app.SystemTypes.SystemObjectType);
            var definition = new FieldDefinition("Value", FieldAttributes.Public, new FieldSignature(valueDefinition.ToTypeSignature()));
            host.Fields.Add(definition);
            field.PutExtraData("AsmResolverField", definition);
            var receiver = new LocalVariable("receiver", new Register(null, "receiver"), app.SystemTypes.SystemObjectType);
            locals.Add(receiver);
            location = new FieldReference(field, receiver, 0);
        }
        if (storage == "array")
        {
            var array = new LocalVariable("array", new Register(null, "array"), new SzArrayTypeAnalysisContext(valueType));
            locals.Add(array);
            location = new ArrayAccess(array, new Immediate(0));
        }
        var instance = storage == "this";
        var constructor = storage == "constructor";
        var target = new InjectedMethodAnalysisContext(instance ? valueType : app.SystemTypes.SystemObjectType,
            constructor ? ".ctor" : "Consume", app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Public
                | (instance || constructor ? 0 : System.Reflection.MethodAttributes.Static), instance ? [] : [parameter]);
        var targetDefinition = new MethodDefinition(target.Name, MethodAttributes.Public | (instance || constructor ? 0 : MethodAttributes.Static),
            instance ? MethodSignature.CreateInstance(module.CorLibTypeFactory.Void)
                : constructor ? MethodSignature.CreateInstance(module.CorLibTypeFactory.Void, [signatureType])
                : MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [signatureType]));
        (instance ? valueDefinition : host).Methods.Add(targetDefinition);
        target.PutExtraData("AsmResolverMethod", targetDefinition);
        var instructions = new List<Instruction>();
        if (constructor)
        {
            var allocated = new LocalVariable("allocated", new Register(null, "allocated"), app.SystemTypes.SystemObjectType);
            locals.Add(allocated);
            instructions.Add(new(0, OpCode.Newobj, allocated, app.SystemTypes.SystemObjectType));
            instructions.Add(new(1, OpCode.CallVoid, target, allocated, new AddressOf(location)));
        }
        else instructions.Add(new(0, OpCode.CallVoid, target, new AddressOf(location)));
        instructions.Add(new(2, OpCode.Return));
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
        {
            Locals = locals, ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph(instructions)
        };
        var generated = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        host.Methods.Add(generated);
        IlGenerator.GenerateIl(caller, generated);
        var il = generated.CilMethodBody!.Instructions;
        Assert.That(il.Count(i => i.OpCode == (constructor ? CilOpCodes.Newobj : CilOpCodes.Call)), Is.EqualTo(1));
        var address = storage switch { "field" => CilOpCodes.Ldflda, "array" => CilOpCodes.Ldelema, _ => CilOpCodes.Ldloca };
        Assert.That(il.Count(i => i.OpCode == address), Is.EqualTo(byRef || instance || storage == "mismatch" ? 1 : 0));
        if (!byRef && !instance && storage != "mismatch")
        {
            var load = storage switch { "field" => CilOpCodes.Ldfld, "array" => CilOpCodes.Ldelem, _ => CilOpCodes.Ldloc };
            Assert.That(il.Any(i => i.OpCode == load), Is.True);
        }
    }
}
