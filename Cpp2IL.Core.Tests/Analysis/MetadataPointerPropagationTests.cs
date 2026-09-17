using System.Collections.Generic;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class MetadataPointerPropagationTests
{
    [TestCase("same", true)]
    [TestCase("different", false)]
    [TestCase("unknown", false)]
    [TestCase("cycle", false)]
    public void ResolvesOnlyUnanimousMetadataAcrossOutOfOrderCopies(string input, bool expected)
    {
        LocalVariable Local(string name) => new(name, new Register(null, name));
        var root = Local("root");
        var other = Local("other");
        var copy = Local("copy");
        var merged = Local("merged");
        var loaded = Local("loaded");
        var metadata = new StringLiteral("metadata");
        var resolved = new Dictionary<LocalVariable, IOperand> { [root] = metadata };
        if (input == "different") resolved[other] = new StringLiteral("different");
        var load = new Instruction(0, OpCode.Move, loaded, new MemoryOperand(merged));
        var phi = new Instruction(1, OpCode.Phi, merged, copy, input switch
        {
            "same" => root,
            "cycle" => merged,
            _ => other,
        });
        var instructions = new[] { load, phi, new Instruction(2, OpCode.Move, copy, root) };

        MetadataResolver.ResolveIndirectMetadataUsages(instructions, resolved);

        Assert.That(Equals(load.Operands[1], metadata), Is.EqualTo(expected));
        Assert.That(resolved.ContainsKey(loaded), Is.EqualTo(expected));
    }

    [TestCase(0, true)]
    [TestCase(8, false)]
    public void DoesNotResolveNonzeroOffsets(long offset, bool expected)
    {
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var loaded = new LocalVariable("loaded", new Register(null, "loaded"));
        var metadata = new StringLiteral("metadata");
        var load = new Instruction(0, OpCode.Move, loaded, new MemoryOperand(pointer, addend: offset));
        MetadataResolver.ResolveIndirectMetadataUsages([load], new() { [pointer] = metadata });
        Assert.That(Equals(load.Operands[1], metadata), Is.EqualTo(expected));
    }
}
