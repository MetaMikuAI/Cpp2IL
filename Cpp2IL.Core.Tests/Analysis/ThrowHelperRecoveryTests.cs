using System;
using System.Collections.Generic;
using System.Text;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ThrowHelperRecoveryTests
{
    // Reports a fixed call graph instead of reading code.
    private sealed class CallGraph(Dictionary<ulong, (ulong[] Data, ulong[] Calls)> graph) : X86InstructionSet
    {
        public override (IReadOnlyList<ulong> DataReferences, IReadOnlyList<ulong> CallTargets) InspectPotentialThrowHelper(
            ApplicationAnalysisContext context, ulong address)
            => graph.TryGetValue(address, out var node) ? (node.Data, node.Calls) : (Array.Empty<ulong>(), Array.Empty<ulong>());
    }

    private static ApplicationAnalysisContext Load(Func<ulong, Dictionary<ulong, (ulong[], ulong[])>> graph)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var name = app.Binary.GetVirtualAddressOfPrimaryExecutableSection();
        app.Binary.BaseStream.Position = app.Binary.MapVirtualAddressToRaw(name);
        app.Binary.BaseStream.Write(Encoding.ASCII.GetBytes("TestException\0"));
        app.InstructionSet = new CallGraph(graph(name));
        return app;
    }

    // Helpers 0x100 -> 0x101 -> ... -> 0x100 + length, where only the last one names what it throws.
    private static Dictionary<ulong, (ulong[], ulong[])> Chain(int length, ulong name)
    {
        var graph = new Dictionary<ulong, (ulong[], ulong[])>();
        for (var i = 0; i < length; i++)
            graph[0x100 + (ulong)i] = (new ulong[0], new[] { 0x100 + (ulong)i + 1 });
        graph[0x100 + (ulong)length] = (new[] { name }, new ulong[0]);
        return graph;
    }

    [Test]
    public void AHelpersNameDoesNotDependOnWhichHelperWasResolvedFirst()
    {
        // The name is five calls below 0x100, past the search depth, and four calls below 0x101.
        var outerFirst = Load(name => Chain(5, name));
        Assert.That(ThrowHelperRecovery.ResolveName(outerFirst, 0x100), Is.Null);
        Assert.That(ThrowHelperRecovery.ResolveName(outerFirst, 0x101), Is.EqualTo("TestException"));

        var innerFirst = Load(name => Chain(5, name));
        Assert.That(ThrowHelperRecovery.ResolveName(innerFirst, 0x101), Is.EqualTo("TestException"));
        Assert.That(ThrowHelperRecovery.ResolveName(innerFirst, 0x100), Is.Null);
    }

    [Test]
    public void AHelperReachedFirstByALongerPathIsSearchedAgainFromAShorterOne()
    {
        // 0x100 reaches 0x104 four calls down through 0x101, then directly; only from there is the
        // helper naming the exception, 0x105, within the search depth.
        var app = Load(name => new Dictionary<ulong, (ulong[], ulong[])>
        {
            [0x100] = (new ulong[0], new ulong[] { 0x101, 0x104 }),
            [0x101] = (new ulong[0], new ulong[] { 0x102 }),
            [0x102] = (new ulong[0], new ulong[] { 0x103 }),
            [0x103] = (new ulong[0], new ulong[] { 0x104 }),
            [0x104] = (new ulong[0], new ulong[] { 0x105 }),
            [0x105] = (new[] { name }, new ulong[0]),
        });
        Assert.That(ThrowHelperRecovery.ResolveName(app, 0x100), Is.EqualTo("TestException"));
    }

    [Test]
    public void HelpersCallingEachOtherEndTheSearch()
    {
        var app = Load(name => new Dictionary<ulong, (ulong[], ulong[])>
        {
            [0x100] = (new ulong[0], new ulong[] { 0x101 }),
            [0x101] = (new ulong[0], new ulong[] { 0x100, 0x102 }),
            [0x102] = (new[] { name }, new ulong[0]),
        });
        Assert.That(ThrowHelperRecovery.ResolveName(app, 0x100), Is.EqualTo("TestException"));
        Assert.That(ThrowHelperRecovery.ResolveName(app, 0x101), Is.EqualTo("TestException"));
    }
}
