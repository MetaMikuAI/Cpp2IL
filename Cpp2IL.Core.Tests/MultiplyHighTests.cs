using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using Disarm;
using MethodAttributes = AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes;
using TypeAttributes = AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes;

namespace Cpp2IL.Core.Tests;

public class MultiplyHighTests
{
    [Test]
    public void ExecutedIlMatchesFullPrecisionSignedProduct()
    {
        var module = new ModuleDefinition("MultiplyHigh" + Guid.NewGuid().ToString("N") + ".dll",
            new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var assembly = new AssemblyDefinition(module.Name!, new Version(1, 0));
        assembly.Modules.Add(module);
        var types = module.CorLibTypeFactory;
        var owner = new TypeDefinition("Tests", "Arithmetic", TypeAttributes.Public, types.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("High", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(types.Int64, [types.Int64, types.Int64]));
        owner.Methods.Add(method);
        method.CilMethodBody = new CilMethodBody { InitializeLocals = true, ComputeMaxStackOnBuild = true };
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_1);
        MultiplyHighEmitter.Emit(method.CilMethodBody);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        using var stream = new MemoryStream();
        module.Write(stream);
        var multiply = Assembly.Load(stream.ToArray()).GetType("Tests.Arithmetic")!.GetMethod("High")!
            .CreateDelegate<Func<long, long, long>>();
        long[] edges = [long.MinValue, long.MinValue + 1, -4294967296, -2147483648, -1, 0, 1,
            2147483647, 4294967295, 4294967296, long.MaxValue - 1, long.MaxValue];
        void Check(long x, long y) => Assert.That(multiply(x, y), Is.EqualTo((long)(((BigInteger)x * y) >> 64)), $"{x} * {y}");
        foreach (var x in edges)
            foreach (var y in edges) Check(x, y);
        var random = new Random(20260922);
        var bytes = new byte[16];
        for (var i = 0; i < 10000; i++)
        {
            random.NextBytes(bytes);
            Check(BitConverter.ToInt64(bytes, 0), BitConverter.ToInt64(bytes, 8));
        }
    }

    [TestCase(0x9b427c20u, false)] // smulh x0, x1, x2
    [TestCase(0x9b417c21u, false)] // destination aliases an input
    [TestCase(0x9b427c3fu, true)]  // destination is XZR
    public void LiftsSignedHighMultiplyWithCorrectDataFlow(uint word, bool discarded)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
            { RawBytes = new BinarySlice(BitConverter.GetBytes(word)) };
        foreach (var name in new[] { "adrpOffsets", "integerConstants" })
            typeof(NewArmV8InstructionSet).GetField(name, BindingFlags.Static | BindingFlags.NonPublic)!
                .SetValue(null, new Dictionary<string, ulong>());
        var decoded = Disassembler.Disassemble(BitConverter.GetBytes(word), 0, new Disassembler.Options(true, true, false)).Single();
        var instructions = new List<Instruction>();
        typeof(NewArmV8InstructionSet).GetMethod("ConvertInstructionStatement", BindingFlags.Instance | BindingFlags.NonPublic)!
            .Invoke(new NewArmV8InstructionSet(), [decoded, instructions, new List<ulong>(), method, new HashSet<string>()]);
        var operation = instructions.Single();
        Assert.That(operation.OpCode, Is.EqualTo(discarded ? OpCode.Nop : OpCode.MultiplyHighSigned));
        if (!discarded)
        {
            Assert.That(operation.Destination, Is.EqualTo(operation.Operands[0]));
            Assert.That(operation.SourcesAndConstants, Is.EquivalentTo(operation.Operands.Skip(1)));
        }
    }

    [Test]
    public void ResultIsInt64WithoutRetypingUnknownInputsAndDeadProductsAreRemoved()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        LocalVariable Local(string name) => new(name, new Register(null, name));
        var x = Local("x"); var y = Local("y"); var result = Local("result");
        var multiply = new Instruction(0, OpCode.MultiplyHighSigned, result, x, y);
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
        {
            Locals = [x, y, result], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph([multiply, new(1, OpCode.Return)])
        };
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(result.Type, Is.SameAs(app.SystemTypes.SystemInt64Type));
        Assert.That(x.Type, Is.Null);
        Assert.That(y.Type, Is.Null);
        DeadCodeEliminator.Run(method);
        Assert.That(method.ControlFlowGraph.Instructions.Any(i => i.OpCode == OpCode.MultiplyHighSigned), Is.False);
    }
}
