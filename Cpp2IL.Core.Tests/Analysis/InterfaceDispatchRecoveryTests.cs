using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;

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
}
