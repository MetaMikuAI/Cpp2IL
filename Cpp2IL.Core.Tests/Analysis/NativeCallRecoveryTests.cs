using System;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests.Analysis;

public class NativeCallRecoveryTests
{
    private const ulong FailFunction = 0x1000;

    [TestCase("sinf", "System.MathF", "Sin", false, 1)]
    [TestCase("atan2f", "System.MathF", "Atan2", false, 2)]
    [TestCase("log10f", "System.MathF", "Log10", false, 1)]
    [TestCase("pow", "System.Math", "Pow", true, 2)]
    [TestCase("acos", "System.Math", "Acos", true, 1)]
    public void MapsMathImportsToTheManagedMethod(string import, string type, string method, bool isDouble, int arity)
        => Assert.That(Arm64ImportResolver.MathFunction(import),
            Is.EqualTo(new Arm64ImportResolver.NativeMathFunction(Arm64ImportResolver.NativeMathKind.Method, type, method, isDouble, arity)));

    [TestCase("fmodf", "Remainder", false)]
    [TestCase("fmod", "Remainder", true)]
    [TestCase("modf", "ModF", true)]
    public void MapsRemainderAndModF(string import, string kind, bool isDouble)
    {
        var function = Arm64ImportResolver.MathFunction(import);
        Assert.That(function?.Kind.ToString(), Is.EqualTo(kind));
        Assert.That(function?.IsDouble, Is.EqualTo(isDouble));
    }

    // exp2f and ldexpf are produced by compiler rewrites of other expressions, sincosf computes two results.
    [TestCase("exp2f")]
    [TestCase("ldexpf")]
    [TestCase("sincosf")]
    [TestCase("memcpy")]
    [TestCase(null)]
    public void LeavesOtherImportsUnmapped(string? import) => Assert.That(Arm64ImportResolver.MathFunction(import), Is.Null);

    [Test]
    public void ResolvesMathImportOnlyToAnExactSignature()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var instructionSet = new NewArmV8InstructionSet();

        var sin = instructionSet.ResolveNativeMathMethod(app, Arm64ImportResolver.MathFunction("sin")!.Value);
        Assert.That(sin, Is.Not.Null);
        Assert.That(sin!.DeclaringType!.FullName, Is.EqualTo("System.Math"));
        Assert.That(sin.ReturnType, Is.EqualTo(app.SystemTypes.SystemDoubleType));
        Assert.That(sin.Parameters.Select(p => p.ParameterType), Is.EqualTo(new[] { app.SystemTypes.SystemDoubleType }));

        // A single-precision function never maps to a double-precision method, which would round differently.
        var sinf = instructionSet.ResolveNativeMathMethod(app, Arm64ImportResolver.MathFunction("sinf")!.Value);
        Assert.That(sinf == null || sinf.DeclaringType!.FullName == "System.MathF"
            && sinf.Parameters.All(p => p.ParameterType == app.SystemTypes.SystemSingleType), Is.True);
    }

    [TestCase(0xD53BD056u, true)] // mrs x22, tpidr_el0
    [TestCase(0xD503201Fu, true)] // nop
    [TestCase(0xD53BD068u, false)] // mrs x8, tpidrro_el0
    [TestCase(0xD53B4200u, false)] // mrs x0, nzcv
    public void TrustsSystemRegisterOnlyWhenEveryReadIsTheThreadPointer(uint word, bool expected)
    {
        var bytes = new byte[8];
        BitConverter.GetBytes(0xD53BD048u).CopyTo(bytes, 0); // mrs x8, tpidr_el0
        BitConverter.GetBytes(word).CopyTo(bytes, 4);
        Assert.That(StackProtectorRecovery.ReadsOnlyThreadPointer(bytes), Is.EqualTo(expected));
    }

    [TestCase("notEqual", true)]
    [TestCase("negatedEqual", true)]
    [TestCase("equalToSuccess", true)]
    [TestCase("mergedCopies", true)]
    [TestCase("mergedOther", false)]
    [TestCase("otherOffset", false)]
    [TestCase("otherBase", false)]
    [TestCase("otherCallee", false)]
    [TestCase("wrongPolarity", false)]
    public void RemovesOnlyStackGuardFailurePaths(string mutation, bool expected)
    {
        var cfg = new ISILControlFlowGraph([]);
        var threadPointer = new LocalVariable("tp", new Register(null, "SYSREG"));
        var otherBase = Local("other");
        var saved = Local("saved");
        var differ = Local("differ");
        var negated = Local("negated");
        var guard = new MemoryOperand(mutation == "otherBase" ? otherBase : threadPointer, addend: mutation == "otherOffset" ? 0x30 : 0x28);
        var entry = Block(cfg, new Instruction(-1, OpCode.Move, saved, new MemoryOperand(threadPointer, addend: 0x28)));
        var success = Block(cfg, new Instruction(-1, OpCode.Return));
        var failCall = new Instruction(-1, OpCode.Call, new Immediate((long)(mutation == "otherCallee" ? FailFunction + 16 : FailFunction)), Local("x0"));
        var failure = Block(cfg, failCall);

        var compare = mutation is "negatedEqual" or "equalToSuccess" or "wrongPolarity" ? OpCode.CheckEqual : OpCode.CheckNotEqual;
        IOperand savedValue = saved;
        if (mutation is "mergedCopies" or "mergedOther")
        {
            // The frame copy reaches the check through a merge.
            var merged = Local("merged");
            var copy = Local("copy");
            entry.AddInstruction(new(-1, OpCode.Move, copy, mutation == "mergedOther" ? new Immediate(0) : saved));
            entry.AddInstruction(new(-1, OpCode.Phi, merged, copy));
            savedValue = merged;
        }
        entry.AddInstruction(new(-1, compare, differ, guard, savedValue));
        var condition = differ;
        if (mutation == "negatedEqual")
        {
            entry.AddInstruction(new(-1, OpCode.Not, negated, differ));
            condition = negated;
        }
        var branch = new Instruction(-1, OpCode.ConditionalJump, mutation == "equalToSuccess" ? success : failure, condition);
        entry.AddInstruction(branch);

        Edge(cfg.EntryBlock, entry);
        Edge(entry, success); Edge(entry, failure);
        Edge(success, cfg.ExitBlock); Edge(failure, cfg.ExitBlock);

        Assert.That(StackProtectorRecovery.Run(cfg, target => target == FailFunction), Is.EqualTo(expected));
        Assert.That(cfg.Blocks.Contains(failure), Is.EqualTo(!expected));
        Assert.That(branch.OpCode, Is.EqualTo(expected ? OpCode.Jump : OpCode.ConditionalJump));
        if (expected)
            Assert.That(entry.Successors, Is.EqualTo(new[] { success }));
    }

    // ldr w8, [x0, #224]; cbz w8, +8; ret; b <class init>
    private static uint[] GuardedClassInit() => [0xB940E008, 0x34000048, 0xD65F03C0, 0x1416A291];

    [Test]
    public void DecodesGuardedTailCall()
        => Assert.That(NewArm64KeyFunctionAddresses.DecodeGuardedTailCall(GuardedClassInit(), 0x43608F0), Is.EqualTo(0x4909340UL));

    [TestCase(0, 0xB940E028u)] // the flag is not read from the first argument
    [TestCase(1, 0x35000048u)] // cbnz: initializes exactly when the flag is set
    [TestCase(1, 0x34000049u)] // tests a register other than the loaded flag
    [TestCase(2, 0xD503201Fu)] // does not return on the other path
    [TestCase(3, 0x9416A291u)] // bl returns into the helper instead of tail-calling
    public void RejectsOtherGuardShapes(int index, uint word)
    {
        var words = GuardedClassInit();
        words[index] = word;
        Assert.That(NewArm64KeyFunctionAddresses.DecodeGuardedTailCall(words, 0x43608F0), Is.Zero);
    }

    private sealed class KeyFunctions : NewArm64KeyFunctionAddresses
    {
        public override void Find(ApplicationAnalysisContext context) => Init(context);

        public void Publish() => InitializeResolvedAddresses();
    }

    private sealed class Arm64 : NewArmV8InstructionSet
    {
        public override BaseKeyFunctionAddresses CreateKeyFunctionAddressesInstance() => new KeyFunctions();
    }

    [TestCase(true)]
    [TestCase(false)] // only a class initializer makes the guarded call a class-initialization call
    public void GuardedCallOfClassInitializerIsClassInitialization(bool initializer)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        app.InstructionSet = new Arm64();
        var code = app.Binary.GetVirtualAddressOfPrimaryExecutableSection();
        var keys = (KeyFunctions)app.GetOrCreateKeyFunctionAddresses();
        if (initializer)
            keys.il2cpp_codegen_runtime_class_init = code + 16;
        else
            keys.il2cpp_vm_object_box = code + 16;
        keys.Publish();

        uint[] words = [0xB940E008, 0x34000048, 0xD65F03C0, 0x14000001]; // b +4 = code + 16
        app.Binary.BaseStream.Position = app.Binary.MapVirtualAddressToRaw(code);
        foreach (var word in words)
            app.Binary.BaseStream.Write(BitConverter.GetBytes(word));

        Assert.That(keys.ResolveKeyFunctionAddress(code), Is.EqualTo(initializer ? code + 16 : 0));
    }

    private static LocalVariable Local(string name) => new(name, new Register(null, name));

    private static Block Block(ISILControlFlowGraph cfg, params Instruction[] instructions)
    {
        var block = new Block { ID = cfg.Blocks.Count, Instructions = instructions.ToList() };
        block.CalculateBlockType();
        cfg.Blocks.Add(block);
        return block;
    }

    private static void Edge(Block from, Block to)
    {
        from.Successors.Add(to);
        to.Predecessors.Add(from);
    }
}
