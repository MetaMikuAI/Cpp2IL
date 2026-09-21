using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterfaceDispatchRecoveryTests
{
    [TestCase(false, false, 0, true)]
    [TestCase(false, false, 2, true)]
    [TestCase(true, false, 2, true)]
    [TestCase(true, true, 2, true)]
    [TestCase(true, true, 3, false)]
    public void MatchesBothAssociationsAndSignedExtendedSlots(bool headerOutside, bool extend, int requestedSlot, bool expected)
        => Check(headerOutside, extend, requestedSlot, expected);

    [TestCase("shift")]
    [TestCase("header")]
    [TestCase("width")]
    [TestCase("class")]
    [TestCase("entry")]
    public void RejectsUnprovenVtableAddressComponents(string invalid)
        => Check(true, true, 2, false, invalid);

    private static void Check(bool headerOutside, bool extend, int slot, bool expected, string invalid = "")
    {
        LocalVariable Local(string name) => new(name, new Register(null, name));
        var receiver = Local("receiver");
        var klass = Local("klass");
        var offset = Local("offset");
        var indexed = Local("indexed");
        var extended = Local("extended");
        var scaled = Local("scaled");
        var sum = Local("sum");
        var address = Local("address");
        var entry = Local("entry");
        var addSlot = slot != 0;
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, klass, invalid == "class" ? new Immediate(10) : new MemoryOperand(receiver)),
            new(1, OpCode.Move, offset, invalid == "entry" ? new Immediate(5) : new MemoryOperand(entry)),
        };
        if (addSlot) instructions.Add(new(2, OpCode.Add, indexed, offset, new Immediate(2)));
        if (extend) instructions.Add(new(3, OpCode.SignExtend, extended, addSlot ? indexed : offset, new Immediate(invalid == "width" ? 16 : 32)));
        instructions.Add(new(4, OpCode.ShiftLeft, scaled, extend ? extended : addSlot ? indexed : offset, new Immediate(invalid == "shift" ? 3 : 4)));
        var header = new Immediate(invalid == "header" ? 0x130 : 0x138);
        instructions.Add(headerOutside ? new(5, OpCode.Add, sum, klass, scaled) : new(5, OpCode.Add, sum, scaled, header));
        var last = headerOutside ? new Instruction(6, OpCode.Add, address, sum, header) : new Instruction(6, OpCode.Add, address, klass, sum);
        instructions.Add(last);
        var definitions = instructions.ToDictionary(i => (LocalVariable)i.Destination!);
        Assert.That(InterfaceDispatchRecovery.MatchVTableEntryChain(definitions, last, slot), Is.SameAs(expected ? klass : null));
    }

    [TestCase("type")]
    [TestCase("slot")]
    [TestCase("runtimeClass")]
    public void ResolvesConstantsAcrossCopiesAndSingleInputPhis(string kind)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        IOperand constant = kind switch
        {
            "type" => app.SystemTypes.SystemObjectType,
            "runtimeClass" => new RuntimeClassTypeAnalysisContext(app.SystemTypes.SystemObjectType, app.SystemTypes.SystemObjectType.DeclaringAssembly),
            _ => new Immediate(2),
        };
        LocalVariable Local(string name) => new(name, new Register(null, name));
        var left = Local("left");
        var join = Local("join");
        var secondJoin = Local("secondJoin");
        var copied = Local("copied");
        var definitions = new Dictionary<LocalVariable, Instruction>
        {
            [left] = new(0, OpCode.Move, left, constant),
            [join] = new(2, OpCode.Phi, join, left),
            [secondJoin] = new(3, OpCode.Phi, secondJoin, join),
            [copied] = new(4, OpCode.Move, copied, secondJoin),
        };
        Assert.That(InterfaceDispatchRecovery.ResolveConstant(definitions, copied), Is.EqualTo(constant));
        Assert.That(InterfaceDispatchRecovery.ResolveConstant(definitions, constant), Is.EqualTo(constant));
    }

    [TestCase("sameConstantJoin")]
    [TestCase("conflict")]
    [TestCase("unknown")]
    [TestCase("load")]
    [TestCase("arithmetic")]
    [TestCase("seedlessArm")]
    [TestCase("seedless")]
    public void DoesNotGuessConflictingUnknownOrSeedlessValues(string shape)
    {
        LocalVariable Local(string name) => new(name, new Register(null, name));
        var first = Local("first");
        var other = Local("other");
        var root = Local("root");
        var definitions = new Dictionary<LocalVariable, Instruction>
        {
            [first] = new(0, OpCode.Move, first, new Immediate(2)),
            [root] = new(2, OpCode.Phi, root, first, other),
        };
        if (shape == "sameConstantJoin") definitions[other] = new(1, OpCode.Move, other, new Immediate(2));
        if (shape == "conflict") definitions[other] = new(1, OpCode.Move, other, new Immediate(3));
        if (shape == "load") definitions[other] = new(1, OpCode.Move, other, new MemoryOperand(first));
        if (shape == "arithmetic") definitions[other] = new(1, OpCode.Add, other, first, new Immediate(0));
        if (shape is "seedlessArm" or "seedless") definitions[other] = new(1, OpCode.Phi, other, other);
        if (shape == "seedless") definitions[root].SetOperands(root, other);
        Assert.That(InterfaceDispatchRecovery.ResolveConstant(definitions, root), Is.Null);
    }
}
