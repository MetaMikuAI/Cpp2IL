using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using Disarm;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class GenericVirtualDispatchTests
{
    private const ulong Helper = 0x4000;

    // target = GetGenericVirtualMethod(receiver->klass->vtable[method->slot].method, method); target->virtualMethodPointer(receiver, target)
    [TestCase("", true)]
    [TestCase("otherReceiver", false)]
    [TestCase("otherMethodSlot", false)]
    [TestCase("vtableHeader", false)]
    [TestCase("methodPointer", false)]
    [TestCase("otherHelper", false)]
    [TestCase("staticMethod", false)]
    public void MatchesVTableGenericVirtualDispatch(string invalid, bool expected)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var objectType = app.SystemTypes.SystemObjectType;
        var generic = GenericMethod(app, objectType, "Convert", invalid == "staticMethod");
        var other = GenericMethod(app, objectType, "Other", false);
        LocalVariable Local(string name) => new(name, new Register(null, name));
        var receiver = Local("receiver");
        var otherObject = Local("otherObject");
        var methodInfo = Local("methodInfo");
        var otherInfo = Local("otherInfo");
        var slot = Local("slot");
        var klass = Local("klass");
        var scaled = Local("scaled");
        var entry = Local("entry");
        var vtableMethod = Local("vtableMethod");
        var target = Local("target");
        var pointer = Local("pointer");
        var hidden = Local("hidden");
        var result = Local("result");
        var helper = new Instruction(7, OpCode.Call, new Immediate(invalid == "otherHelper" ? 0x5000 : (long)Helper), target, vtableMethod, methodInfo);
        var dispatch = new Instruction(10, OpCode.IndirectCall, pointer, result, receiver, hidden);
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, methodInfo, new RuntimeMethodInfoAnalysisContext(generic, objectType.DeclaringAssembly)),
            new(1, OpCode.Move, otherInfo, new RuntimeMethodInfoAnalysisContext(other, objectType.DeclaringAssembly)),
            new(2, OpCode.Move, slot, new MemoryOperand(invalid == "otherMethodSlot" ? otherInfo : methodInfo, addend: 0x50)),
            new(3, OpCode.Move, klass, new MemoryOperand(invalid == "otherReceiver" ? otherObject : receiver)),
            new(4, OpCode.ShiftLeft, scaled, slot, new Immediate(4)),
            new(5, OpCode.Add, entry, klass, scaled),
            new(6, OpCode.Move, vtableMethod, new MemoryOperand(entry, addend: invalid == "vtableHeader" ? 0x138 : 0x140)),
            helper,
            new(8, OpCode.Move, pointer, new MemoryOperand(target, addend: invalid == "methodPointer" ? 0 : 8)),
            new(9, OpCode.Move, hidden, target),
            dispatch,
        };
        var definitions = instructions.Where(i => i != dispatch).ToDictionary(i => (LocalVariable)i.Destination!);

        var match = InterfaceDispatchRecovery.MatchGenericVirtualDispatch(dispatch, definitions, [], address => address == Helper);

        Assert.That(match.HasValue, Is.EqualTo(expected));
        if (!expected)
            return;
        Assert.That(match!.Value.Resolved, Is.SameAs(generic));
        Assert.That(match.Value.Helper, Is.SameAs(helper));
        Assert.That(match.Value.Lookup, Is.Null);
    }

    private static ConcreteGenericMethodAnalysisContext GenericMethod(ApplicationAnalysisContext app, TypeAnalysisContext declaringType, string name, bool isStatic)
    {
        var attributes = MethodAttributes.Public | (isStatic ? MethodAttributes.Static : MethodAttributes.Virtual);
        var definition = new InjectedMethodAnalysisContext(declaringType, name, declaringType, attributes, []);
        definition.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_MVAR,
            GenericParameterAttributes.None, definition));
        return new ConcreteGenericMethodAnalysisContext(definition, [], [app.SystemTypes.SystemStringType]);
    }

    // Object::GetVirtualMethod as compiled for ARM64 (behind il2cpp_object_get_virtual_method): the interface
    // scan loop falls through to the slow path at 0x48DF538 and generic methods tail call 0x49231A0.
    private static readonly uint[] GetVirtualMethod =
    [
        0xf81e0ffe, 0xa9014ff4, 0x79409828, 0xaa0103f3, 0x121b0508, 0x7101011f, 0x540004c1, 0xf9401261,
        0x39446028, 0x372800c8, 0x3940a828, 0x7100791f, 0x54000060, 0x71004d1f, 0x54000441, 0xf9400008,
        0x7940a262, 0x79425d09, 0xb4000129, 0xf940590a, 0x9100214a, 0xf85f814b, 0xeb01017f, 0x540000c0,
        0xf1000529, 0x9100414a, 0x54ffff61, 0x97fe9bfc, 0x14000005, 0xb9400149, 0x0b020129, 0x8b29d108,
        0x9104e100, 0x91002008, 0xf9400114, 0xaa1303e0, 0x94006ae2, 0x360000c0, 0xaa1403e0, 0xaa1303e1,
        0xa9414ff4, 0xf84207fe, 0x17ffab07, 0xaa1403f3, 0xaa1303e0, 0xa9414ff4, 0xf84207fe, 0xd65f03c0,
    ];

    private const int LoopBackEdge = 26;
    private const int GenericTailCall = 42;

    [TestCase(-1, 0x48DF538ul, 0x49231A0ul)]
    [TestCase(GenericTailCall, 0x48DF538ul, 0ul)]
    [TestCase(LoopBackEdge, 0ul, 0x49231A0ul)]
    public void LocatesDispatchHelpersInGetVirtualMethod(int replaced, ulong slowPath, ulong genericVirtualMethod)
    {
        var words = GetVirtualMethod.ToArray();
        if (replaced == GenericTailCall)
            words[replaced] = 0xd65f03c0; // ret: a non-generic build of the helper
        else if (replaced == LoopBackEdge)
            words[replaced] = 0xd503201f; // nop: no scan loop to fall out of
        var bytes = words.SelectMany(BitConverter.GetBytes).ToArray();
        var body = Disassembler.Disassemble(bytes, 0x49384DC, new Disassembler.Options(true, true, false)).ToList();

        Assert.That(NewArm64KeyFunctionAddresses.FindVirtualDispatchHelpers(body), Is.EqualTo((slowPath, genericVirtualMethod)));
    }
}
