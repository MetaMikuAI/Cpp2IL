using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class ConstructorTypePropagationTests
{
    [TestCase("known", true)]
    [TestCase("noAllocation", false)]
    [TestCase("unknownTarget", false)]
    [TestCase("ambiguous", false)]
    public void ResolvesSharedConstructorOnlyAfterAllocationTypeIsProven(string scenario, bool expected)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var root = app.SystemTypes.SystemObjectType;
        var owner = new InjectedTypeAnalysisContext(root.DeclaringAssembly, "Tests", "Container`1", root, TypeAttributes.Public);
        owner.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            GenericParameterAttributes.None, owner));
        var constructor = owner.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType, MethodAttributes.Public,
            root, app.SystemTypes.SystemIntPtrType);
        if (scenario == "ambiguous")
            owner.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType, MethodAttributes.Public,
                app.SystemTypes.SystemStringType, app.SystemTypes.SystemIntPtrType);
        var instance = owner.MakeGenericInstanceType([app.SystemTypes.SystemStringType]);
        var sink = new InjectedMethodAnalysisContext(root, "Use", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, [instance]);
        app.MethodsByAddress[0x1234] = [constructor, new ConcreteGenericMethodAnalysisContext(constructor, [root], [])];
        var metadata = new LocalVariable("metadata", new Register(null, "metadata"));
        var copy = new LocalVariable("copy", new Register(null, "copy"));
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"));
        var existing = new LocalVariable("existing", new Register(null, "existing"), instance);
        var target = new Immediate(scenario == "unknownTarget" ? 0x5678 : 0x1234);
        var call = new Instruction(3, OpCode.CallVoid, target, receiver, new Immediate(0), new Immediate(0));
        var caller = new InjectedMethodAnalysisContext(root, "Caller", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([
                new(0, OpCode.Move, metadata, instance),
                new(1, OpCode.Move, copy, metadata),
                scenario == "noAllocation" ? new(2, OpCode.Move, receiver, existing) : new(2, OpCode.Newobj, receiver, copy),
                call, new(4, OpCode.CallVoid, sink, receiver), new(5, OpCode.Return)]),
            Locals = [metadata, copy, receiver, existing], ParameterLocals = []
        };
        Assert.That(MetadataResolver.ResolveConstructorCalls(caller), Is.False);
        LocalVariables.ResolveTypesAndFields(caller);
        if (expected)
        {
            var resolved = (ConcreteGenericMethodAnalysisContext)call.Operands[0];
            Assert.That(resolved.BaseMethodContext, Is.SameAs(constructor));
            Assert.That(resolved.TypeGenericParameters, Is.EqualTo(instance.GenericArguments));
        }
        else
            Assert.That(call.Operands[0], Is.EqualTo(target));
        Assert.That(MetadataResolver.ResolveConstructorCalls(caller), Is.False, "Resolution must settle");
    }

    // A use (e.g. a Delegate parameter) can type the allocation result before its class operand resolves.
    [TestCase(true)]
    [TestCase(false)]
    public void TheAllocatedClassDecidesTheConstructorOverAWeakerResultType(bool classKnown)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var root = app.SystemTypes.SystemObjectType;
        var owner = new InjectedTypeAnalysisContext(root.DeclaringAssembly, "Tests", "Handler`1", root, TypeAttributes.Public);
        owner.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            GenericParameterAttributes.None, owner));
        var constructor = owner.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType, MethodAttributes.Public,
            root, app.SystemTypes.SystemIntPtrType);
        var instance = owner.MakeGenericInstanceType([app.SystemTypes.SystemStringType]);
        app.MethodsByAddress[0x1234] = [new ConcreteGenericMethodAnalysisContext(constructor, [root], [])];
        var klass = new LocalVariable("klass", new Register(null, "klass"),
            classKnown ? new RuntimeClassTypeAnalysisContext(instance, root.DeclaringAssembly) : null);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), root);
        var target = new Immediate(0x1234);
        var call = new Instruction(1, OpCode.CallVoid, target, receiver, new Immediate(0), new Immediate(0));
        var caller = new InjectedMethodAnalysisContext(root, "Caller", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([new(0, OpCode.Newobj, receiver, klass), call, new(2, OpCode.Return)]),
            Locals = [klass, receiver], ParameterLocals = []
        };

        Assert.That(MetadataResolver.ResolveConstructorCalls(caller), Is.EqualTo(classKnown));
        if (!classKnown)
        {
            Assert.That(call.Operands[0], Is.EqualTo(target), "object has no two-argument constructor to guess");
            return;
        }
        var resolved = (ConcreteGenericMethodAnalysisContext)call.Operands[0];
        Assert.That(resolved.BaseMethodContext, Is.SameAs(constructor));
        Assert.That(resolved.TypeGenericParameters, Is.EqualTo(instance.GenericArguments));
    }
}
