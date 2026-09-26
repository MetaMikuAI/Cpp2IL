using System;
using System.Buffers.Binary;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ForwardingConstructorRecoveryTests
{
    [TestCase(false, 0x2000UL)]
    [TestCase(true, 0x2000UL)]
    [TestCase(false, 0x800UL)]
    [TestCase(true, 0x800UL)]
    public void RecognizesOnlyCompleteTailForwarders(bool clearMetadata, ulong target)
    {
        const ulong start = 0x1000;
        var body = new byte[clearMetadata ? 8 : 4];
        var branchIndex = clearMetadata ? 4 : 0;
        if (clearMetadata) BinaryPrimitives.WriteUInt32LittleEndian(body, 0xAA1F03E1);
        var delta = (long)target - (long)start - branchIndex;
        BinaryPrimitives.WriteUInt32LittleEndian(body.AsSpan(branchIndex), 0x14000000 | (uint)((delta >> 2) & 0x03FFFFFF));
        Assert.That(ForwardingConstructorRecovery.ForwardedTarget(body, start), Is.EqualTo(target));
    }

    [TestCase("e1031faa9ee11615", 0x5BF2EFCUL, 0xA1AB578UL)]
    public void DecodesCapturedForwarder(string hex, ulong start, ulong target)
        => Assert.That(ForwardingConstructorRecovery.ForwardedTarget(Convert.FromHexString(hex), start), Is.EqualTo(target));

    [TestCase(0xAA1F03E0u)] // MOV X0, XZR changes this.
    [TestCase(0xB9000001u)] // STR W1, [X0] initializes a field.
    [TestCase(0x94000001u)] // BL returns to additional code.
    [TestCase(0xD65F03C0u)] // RET alone does not prove the required base call.
    [TestCase(0xD503201Fu)] // Do not skip arbitrary prefix instructions.
    public void RejectsBodiesWhoseEquivalenceIsNotProven(uint prefix)
    {
        var body = new byte[8];
        BinaryPrimitives.WriteUInt32LittleEndian(body, prefix);
        BinaryPrimitives.WriteUInt32LittleEndian(body.AsSpan(4), 0x14000010);
        Assert.That(ForwardingConstructorRecovery.ForwardedTarget(body, 0x1000), Is.Null);
    }

    // Only a call to a further ancestor's parameterless constructor can stand for the base type's.
    [TestCase("base")]
    [TestCase("unrelated")]
    [TestCase("parameters")]
    [TestCase("noCode")]
    public void BaseCallKeepsCallsItCannotProveInlined(string scenario)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        app.InstructionSet = new NewArmV8InstructionSet();
        var root = app.SystemTypes.SystemObjectType;
        var corlib = root.DeclaringAssembly;
        var grandparent = corlib.InjectType("Tests", "Grandparent", root, TypeAttributes.Public);
        var parent = corlib.InjectType("Tests", "Parent", grandparent, TypeAttributes.Public);
        var child = corlib.InjectType("Tests", "Child", parent, TypeAttributes.Public);
        var unrelated = corlib.InjectType("Tests", "Unrelated", root, TypeAttributes.Public);
        var owner = scenario switch { "base" => parent, "unrelated" => unrelated, _ => grandparent };
        var called = scenario == "parameters"
            ? owner.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType, MethodAttributes.Public, app.SystemTypes.SystemInt32Type)
            : owner.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType, MethodAttributes.Public);
        // Injected methods have no native code, so only the checks before reading the binary are exercised.
        Assert.That(ForwardingConstructorRecovery.ResolveBaseCall(child, called), Is.Null);
    }

    [TestCase(0)]
    [TestCase(3)]
    [TestCase(4)]
    [TestCase(7)]
    public void RejectsTruncatedMetadataClearAndBranch(int length)
    {
        var body = Convert.FromHexString("e1031faa9ee11615");
        Assert.That(ForwardingConstructorRecovery.ForwardedTarget(body.AsSpan(0, length), 0x5BF2EFC), Is.Null);
    }
}
