using System.Collections.Generic;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class MergedBaseFieldTests
{
    // A load through phi(inputs) at offset 0: resolvable only when every input addresses the same member.
    [TestCase("storageAndInterior", false)]
    [TestCase("storageAndObject", false)]
    [TestCase("objectAndInterior", false)]
    [TestCase("objectAndConstant", false)]
    [TestCase("objects", true)]
    [TestCase("sameStorage", true)]
    [TestCase("separateSlots", false)]
    [TestCase("objectAndNull", true)]
    public void ResolvesMergedBaseOnlyForOneMember(string inputs, bool resolvable)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var type = app.SystemTypes.SystemStringType;
        TypeAnalysisContext Storage() => new StaticFieldStorageTypeAnalysisContext(type, type.DeclaringAssembly);
        var definitions = new Dictionary<LocalVariable, Instruction>();
        LocalVariable Local(string name, TypeAnalysisContext? t) => new(name, new Register(null, name), t);
        LocalVariable Defined(string name, TypeAnalysisContext? t, OpCode opCode, params IOperand[] sources)
        {
            var local = Local(name, t);
            definitions[local] = new Instruction(0, opCode, [local, ..sources]);
            return local;
        }
        var receiver = Local("receiver", type);
        var klass = Local("klass", new RuntimeClassTypeAnalysisContext(type, type.DeclaringAssembly));
        IOperand[] sources = inputs switch
        {
            "storageAndInterior" => [Defined("storage", Storage(), OpCode.Move, new MemoryOperand(klass, addend: 0xB8)),
                Defined("interior", type, OpCode.Add, receiver, new Immediate(0x30))],
            "storageAndObject" => [Defined("storage", Storage(), OpCode.Move, new MemoryOperand(klass, addend: 0xB8)), receiver],
            "objectAndInterior" => [receiver, Defined("interior", type, OpCode.Add, receiver, new Immediate(8))],
            "objectAndConstant" => [receiver, new Immediate(0x1234)],
            "objects" => [receiver, Local("other", type)],
            "sameStorage" => [Defined("storage", Storage(), OpCode.Move, new MemoryOperand(klass, addend: 0xB8)),
                Defined("storage2", Storage(), OpCode.Move, new MemoryOperand(klass, addend: 0xB8))],
            "separateSlots" => [Defined("slot", Storage(), OpCode.Move, new MemoryOperand(addend: 0x1000)),
                Defined("slot2", Storage(), OpCode.Move, new MemoryOperand(addend: 0x1008))],
            _ => [receiver, new Immediate(0)],
        };
        var first = sources[0] as LocalVariable;
        var merged = Defined("merged", first?.Type, OpCode.Phi, sources);
        var copy = Defined("copy", merged.Type, OpCode.Move, merged);
        Assert.That(MetadataResolver.MergedBaseAgrees(copy, 0, definitions), Is.EqualTo(resolvable));
    }
}
