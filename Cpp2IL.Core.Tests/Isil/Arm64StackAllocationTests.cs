using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using MethodAttributes = AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes;
using TypeAttributes = AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes;

namespace Cpp2IL.Core.Tests.Isil;

public class Arm64StackAllocationTests
{
    // alloca(sizeof(T)) in a fully shared generic method:
    // mov x8, sp; add x9, x2, #0xf; and x9, x9, #0x1fffffff0; sub x20, x8, x9; mov sp, x20
    private static readonly uint[] Allocation = [0x910003E8u, 0x91003C49u, 0x927C7129u, 0xCB090114u, 0x9100029Fu];

    [Test]
    public void DynamicStackAllocationBecomesLocalAllocate()
    {
        var instructions = Lift(Allocation);
        var allocation = instructions.Single(i => i.OpCode == OpCode.LocalAllocate);
        Assert.That(allocation.Destination, Is.EqualTo(new Register(null, "X20")));
        Assert.That(allocation.Operands[1], Is.EqualTo(new Register(null, "X9")));
        Assert.That(instructions.Any(i => i.OpCode == OpCode.Subtract), Is.False);
        Assert.That(instructions[^1].OpCode, Is.EqualTo(OpCode.Nop));
    }

    [Test]
    public void AllocationMayReuseTheStackCopyRegister()
    {
        // mov x8, sp; stur x9, [x29, #-96]; add x9, x9, #0xf; and x9, x9, #0x1fffffff0; sub x8, x8, x9;
        // stur x8, [x29, #-64]; mov sp, x8
        var instructions = Lift([0x910003E8u, 0xF81A03A9u, 0x91003D29u, 0x927C7129u, 0xCB090108u, 0xF81C03A8u, 0x9100011Fu]);
        var allocation = instructions.Single(i => i.OpCode == OpCode.LocalAllocate);
        Assert.That(allocation.Destination, Is.EqualTo(new Register(null, "X8")));
        Assert.That(allocation.Operands[1], Is.EqualTo(new Register(null, "X9")));
    }

    [Test]
    public void BranchBetweenStackCopyAndSubtractionIsNotAnAllocation()
    {
        // cbz x9, #8 between the copy of sp and the subtraction
        var instructions = Lift([0x910003E8u, 0xB4000049u, 0xCB090114u, 0x9100029Fu]);
        Assert.That(instructions.Any(i => i.OpCode == OpCode.LocalAllocate), Is.False);
        Assert.That(instructions.Count(i => i.OpCode == OpCode.Subtract), Is.EqualTo(1));
    }

    [Test]
    public void FramePointerRestoreIsNotAnAllocation()
    {
        // mov x29, sp; mov sp, x29
        var instructions = Lift([0x910003FDu, 0x910003BFu]);
        Assert.That(instructions.Any(i => i.OpCode == OpCode.LocalAllocate), Is.False);
    }

    [Test]
    public void LocalAllocateEmitsLocallocOfAnUnsignedNativeSize()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var pointer = new LocalVariable("buffer", new Register(null, "buffer"), app.SystemTypes.SystemByteType.MakePointerType());
        var size = new LocalVariable("size", new Register(null, "size"), app.SystemTypes.SystemUInt64Type);
        var il = Generate([new Instruction(0, OpCode.LocalAllocate, pointer, size)], [pointer, size]);
        var localloc = il.FindIndex(i => i.OpCode == CilOpCodes.Localloc);
        Assert.That(localloc, Is.GreaterThan(1));
        Assert.That(il[localloc - 1].OpCode, Is.EqualTo(CilOpCodes.Conv_U));
        Assert.That(il[localloc + 1].OpCode.Code, Is.EqualTo(CilCode.Stloc));
    }

    [Test]
    public void BoxingAStackAllocationReadsTheValueThroughTheAddress()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var pointer = new LocalVariable("buffer", new Register(null, "buffer"), app.SystemTypes.SystemByteType.MakePointerType());
        var boxed = new LocalVariable("boxed", new Register(null, "boxed"), app.SystemTypes.SystemObjectType);
        var il = Generate([new Instruction(0, OpCode.Box, boxed, app.SystemTypes.SystemInt32Type, pointer)], [pointer, boxed]);
        var box = il.FindIndex(i => i.OpCode == CilOpCodes.Box);
        Assert.That(box, Is.GreaterThan(1));
        Assert.That(il[box - 1].OpCode, Is.EqualTo(CilOpCodes.Ldobj));
        Assert.That(il[box - 2].OpCode.Code, Is.EqualTo(CilCode.Ldloc));
    }

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    private static List<Instruction> Lift(uint[] words)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, []);
        typeof(NewArmV8InstructionSet).GetField("adrpOffsets", BindingFlags.NonPublic | BindingFlags.Static)!
            .SetValue(null, new Dictionary<string, ulong>());
        typeof(NewArmV8InstructionSet).GetField("integerConstants", BindingFlags.NonPublic | BindingFlags.Static)!
            .SetValue(null, new Dictionary<string, ulong>());
        var bytes = words.SelectMany(BitConverter.GetBytes).ToArray();
        var convert = typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement", BindingFlags.NonPublic | BindingFlags.Instance)!;
        var instructionSet = new NewArmV8InstructionSet();
        var instructions = new List<Instruction>();
        var addresses = new List<ulong>();
        foreach (var decoded in Disassembler.Disassemble(bytes, 0x1000, new Disassembler.Options(true, true, false)))
            convert.Invoke(instructionSet, [decoded, instructions, addresses, caller, new HashSet<string>()]);
        return instructions;
    }

    private static List<CilInstruction> Generate(List<Instruction> body, List<LocalVariable> locals)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        body.Add(new Instruction(body.Count, OpCode.Return));
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph(body),
            Locals = locals, ParameterLocals = [], AnalysisWarnings = []
        };
        var module = new ModuleDefinition("Test.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        foreach (var context in new[] { app.SystemTypes.SystemByteType, app.SystemTypes.SystemUInt64Type,
                     app.SystemTypes.SystemObjectType, app.SystemTypes.SystemInt32Type })
        {
            var placeholder = new TypeDefinition(context.Namespace, context.Name, TypeAttributes.Public);
            module.TopLevelTypes.Add(placeholder);
            context.PutExtraData("AsmResolverType", placeholder);
        }
        var type = new TypeDefinition("Tests", "Recovery", TypeAttributes.Public);
        module.TopLevelTypes.Add(type);
        var definition = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(definition);
        IlGenerator.GenerateIl(caller, definition);
        return definition.CilMethodBody!.Instructions.ToList();
    }
}
