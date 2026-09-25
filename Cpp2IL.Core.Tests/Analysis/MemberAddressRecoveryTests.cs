using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class MemberAddressRecoveryTests
{
    private static MethodAnalysisContext Method(ApplicationAnalysisContext app, params Instruction[] instructions) =>
        new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Address", app.SystemTypes.SystemVoidType,
            MethodAttributes.Static | MethodAttributes.Public, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([.. instructions, new Instruction(instructions.Length, OpCode.Return)]),
            Locals = [], ParameterLocals = []
        };

    // UnityEngine.Bounds is { Vector3 m_Center @0; Vector3 m_Extents @12 }.
    [TestCase("inside", true)]
    [TestCase("pointer", true)]
    [TestCase("argument", true)]
    [TestCase("pastMember", false)]
    [TestCase("unknownWidth", false)]
    [TestCase("noMember", false)]
    [TestCase("typedResult", false)]
    [TestCase("typedPointer", true)]
    [TestCase("otherPointer", false)]
    [TestCase("arithmetic", false)]
    [TestCase("unused", false)]
    [TestCase("assignedReceiver", false)]
    public void StructStorageOffsetIsTheMemberAddress(string shape, bool expected)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var bounds = app.AllTypes.Single(t => t.FullName == "UnityEngine.Bounds");
        var extents = bounds.Fields.Single(f => f.Name == "m_Extents");
        var storage = new LocalVariable("storage", new Register(null, "storage"), shape == "pointer" ? new ByRefTypeAnalysisContext(bounds) : bounds);
        var address = new LocalVariable("address", new Register(null, "address"), shape switch
        {
            "typedResult" => app.SystemTypes.SystemObjectType,
            "typedPointer" => new ByRefTypeAnalysisContext(extents.FieldType),
            "otherPointer" => new ByRefTypeAnalysisContext(app.SystemTypes.SystemInt32Type),
            _ => null
        });
        var loaded = new LocalVariable("loaded", new Register(null, "loaded"));
        var consume = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Consume", app.SystemTypes.SystemVoidType,
            MethodAttributes.Static | MethodAttributes.Public, [new ByRefTypeAnalysisContext(extents.FieldType)]);
        var add = new Instruction(0, OpCode.Add, address, shape == "pointer" ? storage : new AddressOf(storage),
            new Immediate(shape == "noMember" ? 13 : extents.Offset));
        var use = shape switch
        {
            "argument" => new Instruction(1, OpCode.CallVoid, consume, address),
            "pastMember" => new Instruction(1, OpCode.Move, loaded, new MemoryOperand(address, addend: 12, accessSize: 4)),
            "unknownWidth" => new Instruction(1, OpCode.Move, loaded, new MemoryOperand(address, addend: 4)),
            "arithmetic" => new Instruction(1, OpCode.Add, loaded, address, new Immediate(4)),
            "unused" => new Instruction(1, OpCode.Nop),
            _ => new Instruction(1, OpCode.Move, loaded, new MemoryOperand(address, addend: 4, accessSize: 4)),
        };

        var instructions = shape == "assignedReceiver"
            ? new[] { new Instruction(0, OpCode.Move, storage, new LocalVariable("copy", new Register(null, "copy"), bounds)), add, use }
            : new[] { add, use };
        Assert.That(LocalVariables.RecoverMemberAddresses(Method(app, instructions)), Is.EqualTo(expected));
        if (!expected)
        {
            Assert.That(add.OpCode, Is.EqualTo(OpCode.Add));
            return;
        }
        Assert.That(add.OpCode, Is.EqualTo(OpCode.Move));
        var member = (FieldReference)((AddressOf)add.Operands[1]).Target;
        Assert.That(member.Field, Is.SameAs(extents));
        Assert.That(member.Local, Is.SameAs(storage));
        Assert.That(address.Type, Is.InstanceOf<ByRefTypeAnalysisContext>());
        Assert.That(((ByRefTypeAnalysisContext)address.Type!).ElementType, Is.SameAs(extents.FieldType));
    }

    [TestCase(true, true)]
    [TestCase(false, false)]
    public void ObjectOffsetIsRecoveredOnlyForCallArguments(bool argument, bool expected)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var owner = app.AllTypes.Single(t => t.FullName == "UnityEngine.Object");
        var field = owner.Fields.Single(f => f.Name == "m_CachedPtr");
        var instance = new LocalVariable("instance", new Register(null, "instance"), owner);
        var address = new LocalVariable("address", new Register(null, "address"));
        var loaded = new LocalVariable("loaded", new Register(null, "loaded"));
        var consume = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Consume", app.SystemTypes.SystemVoidType,
            MethodAttributes.Static | MethodAttributes.Public, [new ByRefTypeAnalysisContext(field.FieldType)]);
        var add = new Instruction(0, OpCode.Add, address, instance, new Immediate(field.Offset));
        var use = argument
            ? new Instruction(1, OpCode.CallVoid, consume, address)
            : new Instruction(1, OpCode.Move, loaded, new MemoryOperand(address, addend: 0, accessSize: 8));

        Assert.That(LocalVariables.RecoverMemberAddresses(Method(app, add, use)), Is.EqualTo(expected));
        Assert.That(add.OpCode, Is.EqualTo(expected ? OpCode.Move : OpCode.Add));
        if (expected)
            Assert.That(((FieldReference)((AddressOf)add.Operands[1]).Target).Field, Is.SameAs(field));
    }
}
