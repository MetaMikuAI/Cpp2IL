using System;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Runtime.CompilerServices;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using FieldAttributes = AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes;
using MethodAttributes = AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes;
using MethodImplAttributes = AsmResolver.PE.DotNet.Metadata.Tables.MethodImplAttributes;
using PropertyAttributes = AsmResolver.PE.DotNet.Metadata.Tables.PropertyAttributes;
using TypeAttributes = AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes;

namespace Cpp2IL.Core.Tests;

public class ProvenGetterReadRecoveryTests
{
    private static (ModuleDefinition Module, FieldDefinition Field, MethodDefinition Getter, MethodDefinition Reader, CilInstruction Read) Build(bool isStatic = false)
    {
        var module = new ModuleDefinition("Getter" + Guid.NewGuid().ToString("N") + ".dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        new AssemblyDefinition(module.Name!, new Version(1, 0)).Modules.Add(module);
        var owner = new TypeDefinition("Tests", "Target", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var field = new FieldDefinition("value", FieldAttributes.Private | (isStatic ? FieldAttributes.Static : 0), new FieldSignature(module.CorLibTypeFactory.Int32));
        owner.Fields.Add(field);
        var getter = AddGetter(owner, field, "Value");
        var caller = new TypeDefinition("Tests", "Caller", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(caller);
        var reader = new MethodDefinition("Read", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32, isStatic ? [] : [owner.ToTypeSignature()]));
        caller.Methods.Add(reader);
        reader.CilMethodBody = new CilMethodBody { ComputeMaxStackOnBuild = true };
        if (!isStatic)
            reader.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
        var read = new CilInstruction(isStatic ? CilOpCodes.Ldsfld : CilOpCodes.Ldfld, field);
        reader.CilMethodBody.Instructions.Add(read);
        reader.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        return (module, field, getter, reader, read);
    }

    private static MethodDefinition AddGetter(TypeDefinition owner, FieldDefinition field, string name)
    {
        var signature = field.IsStatic ? MethodSignature.CreateStatic(field.Signature!.FieldType) : MethodSignature.CreateInstance(field.Signature!.FieldType);
        var getter = new MethodDefinition("get_" + name, MethodAttributes.Public | MethodAttributes.SpecialName | (field.IsStatic ? MethodAttributes.Static : 0), signature);
        owner.Methods.Add(getter);
        getter.CilMethodBody = new CilMethodBody { ComputeMaxStackOnBuild = true };
        if (!field.IsStatic)
            getter.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
        getter.CilMethodBody.Instructions.Add(field.IsStatic ? CilOpCodes.Ldsfld : CilOpCodes.Ldfld, field);
        getter.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        var property = new PropertyDefinition(name, PropertyAttributes.None, field.IsStatic ? PropertySignature.CreateStatic(field.Signature.FieldType) : PropertySignature.CreateInstance(field.Signature.FieldType));
        property.SetSemanticMethods(getter, null);
        owner.Properties.Add(property);
        return getter;
    }

    [TestCase(true, true)]
    [TestCase(false, false)]
    public void StructGetter_IsCalledOnlyThroughAnAddress(bool throughAddress, bool recovered)
    {
        var module = new ModuleDefinition("Struct" + Guid.NewGuid().ToString("N") + ".dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        new AssemblyDefinition(module.Name!, new Version(1, 0)).Modules.Add(module);
        var valueType = module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType");
        var owner = new TypeDefinition("Tests", "Target", TypeAttributes.Public | TypeAttributes.Sealed, valueType);
        module.TopLevelTypes.Add(owner);
        var field = new FieldDefinition("value", FieldAttributes.Private, new FieldSignature(module.CorLibTypeFactory.Int32));
        owner.Fields.Add(field);
        var getter = AddGetter(owner, field, "Value");
        var caller = new TypeDefinition("Tests", "Caller", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(caller);
        var reader = new MethodDefinition("Read", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32, [owner.ToTypeSignature()]));
        caller.Methods.Add(reader);
        reader.CilMethodBody = new CilMethodBody { ComputeMaxStackOnBuild = true };
        reader.CilMethodBody.Instructions.Add(throughAddress ? CilOpCodes.Ldarga_S : CilOpCodes.Ldarg, reader.Parameters[0]);
        var read = new CilInstruction(CilOpCodes.Ldfld, field);
        reader.CilMethodBody.Instructions.Add(read);
        reader.CilMethodBody.Instructions.Add(CilOpCodes.Ret);

        Assert.That(ProvenGetterReadRecovery.Recover(module).Reads, Is.EqualTo(recovered ? 1 : 0));
        if (recovered)
            Assert.That((read.OpCode, read.Operand), Is.EqualTo((CilOpCodes.Call, (object)getter)), "a struct's getter is called, not called virtually");
    }

    [TestCase(true)]
    [TestCase(false)]
    public void StoreFromAnotherType_GoesThroughTheProvenSetter(bool trivial)
    {
        var (module, field, _, reader, _) = Build();
        var owner = field.DeclaringType!;
        var setter = new MethodDefinition("set_Value", MethodAttributes.Public | MethodAttributes.SpecialName,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.Int32]));
        owner.Methods.Add(setter);
        setter.CilMethodBody = new CilMethodBody { ComputeMaxStackOnBuild = true };
        setter.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
        // As generated: the value parameter in its long form.
        setter.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg, setter.Parameters[0]);
        if (!trivial)
        {
            setter.CilMethodBody.Instructions.Add(CilOpCodes.Ldc_I4_1);
            setter.CilMethodBody.Instructions.Add(CilOpCodes.Add);
        }
        setter.CilMethodBody.Instructions.Add(CilOpCodes.Stfld, field);
        setter.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        owner.Properties.Single(p => p.Name == "Value").SetMethod = setter;
        var writer = new MethodDefinition("Write", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [owner.ToTypeSignature()]));
        reader.DeclaringType!.Methods.Add(writer);
        writer.CilMethodBody = new CilMethodBody { ComputeMaxStackOnBuild = true };
        writer.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
        writer.CilMethodBody.Instructions.Add(CilOpCodes.Ldc_I4_5);
        var store = writer.CilMethodBody.Instructions.Add(CilOpCodes.Stfld, field);
        writer.CilMethodBody.Instructions.Add(CilOpCodes.Ret);

        ProvenGetterReadRecovery.Recover(module);

        Assert.That(store.OpCode, Is.EqualTo(trivial ? CilOpCodes.Callvirt : CilOpCodes.Stfld));
    }

    [Test]
    public void InstanceRead_ExecutesWithNullCheckAndPreservesBranchTarget()
    {
        var (module, field, getter, reader, read) = Build();
        var label = new CilInstructionLabel(read);
        reader.CilMethodBody!.Instructions.Insert(1, new CilInstruction(CilOpCodes.Br, label));
        Assert.That(ProvenGetterReadRecovery.Recover(module), Is.EqualTo(new ProvenGetterReadRecovery.Result(1, 1)));
        Assert.That(label.Instruction, Is.SameAs(read));
        Assert.That(read.OpCode, Is.EqualTo(CilOpCodes.Callvirt));
        Assert.That(getter.CilMethodBody!.Instructions[1].OpCode, Is.EqualTo(CilOpCodes.Ldfld));
        using var stream = new MemoryStream();
        module.Write(stream);
        var assembly = Assembly.Load(stream.ToArray());
        var target = assembly.GetType("Tests.Target")!;
        var value = RuntimeHelpers.GetUninitializedObject(target);
        target.GetField(field.Name!, BindingFlags.Instance | BindingFlags.NonPublic)!.SetValue(value, 42);
        var invoke = assembly.GetType("Tests.Caller")!.GetMethod("Read")!;
        Assert.That(invoke.Invoke(null, [value]), Is.EqualTo(42));
        Assert.That(() => invoke.Invoke(null, [null]), Throws.TypeOf<TargetInvocationException>().With.InnerException.TypeOf<NullReferenceException>());
    }

    [Test]
    public void StaticRead_StillRunsTypeInitializer()
    {
        var (module, field, _, _, read) = Build(true);
        var cctor = new MethodDefinition(".cctor", MethodAttributes.Private | MethodAttributes.Static | MethodAttributes.SpecialName | MethodAttributes.RuntimeSpecialName, MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        field.DeclaringType!.Methods.Add(cctor);
        cctor.CilMethodBody = new CilMethodBody { ComputeMaxStackOnBuild = true };
        cctor.CilMethodBody.Instructions.Add(CilOpCodes.Ldc_I4, 73);
        cctor.CilMethodBody.Instructions.Add(CilOpCodes.Stsfld, field);
        cctor.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        Assert.That(ProvenGetterReadRecovery.Recover(module).Reads, Is.EqualTo(1));
        Assert.That(read.OpCode, Is.EqualTo(CilOpCodes.Call));
        using var stream = new MemoryStream();
        module.Write(stream);
        var assembly = Assembly.Load(stream.ToArray());
        Assert.That(assembly.GetType("Tests.Caller")!.GetMethod("Read")!.Invoke(null, null), Is.EqualTo(73));
    }

    [Test]
    public void TwoGetters_KeepOneDirectReadAndCannotFormACycle()
    {
        var (module, field, getter, _, _) = Build();
        var second = AddGetter(field.DeclaringType!, field, "Other");
        var result = ProvenGetterReadRecovery.Recover(module);
        Assert.That(result, Is.EqualTo(new ProvenGetterReadRecovery.Result(1, 2)));
        Assert.That(getter.CilMethodBody!.Instructions[1].OpCode, Is.EqualTo(CilOpCodes.Ldfld));
        Assert.That(second.CilMethodBody!.Instructions[1].Operand, Is.SameAs(getter));
        Assert.That(ProvenGetterReadRecovery.Recover(module).Reads, Is.Zero);
    }

    [TestCase("virtual")]
    [TestCase("pinvoke")]
    [TestCase("synchronized")]
    [TestCase("wrongReturn")]
    [TestCase("byrefReturn")]
    [TestCase("generic")]
    [TestCase("nontrivial")]
    [TestCase("volatile")]
    [TestCase("unaligned")]
    [TestCase("address")]
    [TestCase("constructor")]
    public void UnprovenOrSpecialAccess_RemainsUnchanged(string kind)
    {
        var (module, _, getter, reader, read) = Build();
        switch (kind)
        {
            case "virtual": getter.IsVirtual = true; break;
            case "pinvoke": getter.IsPInvokeImpl = true; break;
            case "synchronized": getter.ImplAttributes |= MethodImplAttributes.Synchronized; break;
            case "wrongReturn": getter.Signature!.ReturnType = module.CorLibTypeFactory.Int64; break;
            case "byrefReturn": getter.Signature!.ReturnType = new ByReferenceTypeSignature(module.CorLibTypeFactory.Int32); break;
            case "generic": getter.DeclaringType!.GenericParameters.Add(new GenericParameter("T")); break;
            // Anything beyond the field read, but for nops, makes the getter more than the field.
            case "nontrivial":
                getter.CilMethodBody!.Instructions.Insert(0, new CilInstruction(CilOpCodes.Ldnull));
                getter.CilMethodBody!.Instructions.Insert(1, new CilInstruction(CilOpCodes.Pop));
                break;
            case "volatile": reader.CilMethodBody!.Instructions.Insert(1, new CilInstruction(CilOpCodes.Volatile)); break;
            case "unaligned": reader.CilMethodBody!.Instructions.Insert(1, new CilInstruction(CilOpCodes.Unaligned, (byte)1)); break;
            case "address": read.OpCode = CilOpCodes.Ldflda; break;
            case "constructor": reader.Name = ".ctor"; break;
        }
        var original = read.OpCode;
        Assert.That(ProvenGetterReadRecovery.Recover(module).Reads, Is.Zero);
        Assert.That(read.OpCode, Is.EqualTo(original));
    }
}
