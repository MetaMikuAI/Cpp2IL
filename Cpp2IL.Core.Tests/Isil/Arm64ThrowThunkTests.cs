using System;
using Cpp2IL.Core.InstructionSets;

namespace Cpp2IL.Core.Tests.Isil;

public class Arm64ThrowThunkTests
{
    [Test]
    public void DoesNotFollowLateBranchFromAdjacentCodeAfterNonReturningCall()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var address = app.Binary.GetVirtualAddressOfPrimaryExecutableSection();
        app.Binary.BaseStream.Position = app.Binary.MapVirtualAddressToRaw(address);
        foreach (var word in new[] { 0xF81F0FFEu, 0x94000008u, 0x90000000u, 0x91000000u, 0x14000010u })
            app.Binary.BaseStream.Write(BitConverter.GetBytes(word));
        var (_, calls) = new NewArmV8InstructionSet().InspectPotentialThrowHelper(app, address);
        Assert.That(calls, Is.EqualTo(new[] { address + 4 + 32 }));
    }

    [TestCase(0x14000008u, true)] // B +32
    [TestCase(0xD61F0000u, false)] // BR X0: unknown target
    [TestCase(0xD65F03C0u, false)] // RET
    public void InspectsDirectTailThunkWithoutReadingTheNextFunction(uint word, bool expected)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var address = app.Binary.GetVirtualAddressOfPrimaryExecutableSection();
        app.Binary.BaseStream.Position = app.Binary.MapVirtualAddressToRaw(address);
        app.Binary.BaseStream.Write(BitConverter.GetBytes(word));
        app.Binary.BaseStream.Write(BitConverter.GetBytes(0x94000010u)); // neighboring BL must not be scanned
        app.Binary.BaseStream.Write(BitConverter.GetBytes(0xD65F03C0u));
        var (_, calls) = new NewArmV8InstructionSet().InspectPotentialThrowHelper(app, address);
        Assert.That(calls.Count, Is.EqualTo(expected ? 1 : 0));
        if (expected) Assert.That(calls[0], Is.EqualTo(address + 32));
    }
}
