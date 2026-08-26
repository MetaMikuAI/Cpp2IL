using Cpp2IL.Core.InstructionSets;
using Iced.Intel;

namespace Cpp2IL.Core.Tests.Isil;

public class X86SwitchRecognizerTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [Test]
    public void ComparisonCascadeProducesCompleteSwitch()
    {
        const ulong baseAddress = 0x1000;
        byte[] bytes =
        [
            0x89, 0xD0,             // mov eax, edx
            0x85, 0xD2,             // test edx, edx
            0x74, 0x10,             // je case 0
            0x83, 0xE8, 0x01,       // sub eax, 1
            0x74, 0x0C,             // je case 1
            0x83, 0xE8, 0x01,       // sub eax, 1
            0x74, 0x08,             // je case 2
            0x83, 0xF8, 0x01,       // cmp eax, 1
            0x74, 0x04,             // je case 3
            0xC3,                   // default
            0xC3, 0xC3, 0xC3, 0xC3 // cases 0-3
        ];

        var decoder = Decoder.Create(64, new ByteArrayCodeReader(bytes));
        decoder.IP = baseAddress;
        var instructions = new InstructionList();
        while (decoder.IP < baseAddress + (ulong)bytes.Length)
            instructions.Add(decoder.Decode());

        var appContext = Cpp2IlApi.CurrentAppContext!;
        var method = appContext.AssembliesByName["mscorlib"]
            .GetTypeByFullName("System.AppDomain")!
            .GetMethod("DoDomainUnload");
        var dispatches = X86SwitchRecognizer.Find(method, instructions);

        Assert.That(dispatches, Has.Count.EqualTo(1));
        var dispatch = dispatches[0];
        Assert.Multiple(() =>
        {
            Assert.That(dispatch.StartIndex, Is.Zero);
            Assert.That(dispatch.EndIndex, Is.EqualTo(8));
            Assert.That(dispatch.Selector, Is.EqualTo(Register.EDX));
            Assert.That(dispatch.SelectorSize, Is.EqualTo(4));
            Assert.That(dispatch.DefaultTarget, Is.EqualTo(baseAddress + 0x15));
            Assert.That(dispatch.CaseTargets, Is.EqualTo(new ulong[]
            {
                baseAddress + 0x16,
                baseAddress + 0x17,
                baseAddress + 0x18,
                baseAddress + 0x19
            }));
        });
    }
}
