using System;
using System.IO;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using TypeAttributes = AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes;
using MethodAttributes = AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes;

namespace Cpp2IL.Core.Tests;

public class NumericConversionTests
{
    private ApplicationAnalysisContext _app = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
    }

    private TypeAnalysisContext Type(string name) => _app.AllTypes.Single(t => t.FullName == "System." + name);

    private MethodInfo Compile(string source, string target, int rounding = 0, int fractionalBits = 0)
    {
        var module = new ModuleDefinition("Conversion" + Guid.NewGuid().ToString("N") + ".dll",
            new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var assembly = new AssemblyDefinition(module.Name!, new Version(1, 0));
        assembly.Modules.Add(module);
        var owner = new TypeDefinition("Tests", "Numeric", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var types = module.CorLibTypeFactory;
        TypeSignature Signature(string name) => name switch
        {
            "Single" => types.Single, "Double" => types.Double,
            "Int32" => types.Int32, "UInt32" => types.UInt32,
            "Int64" => types.Int64, "UInt64" => types.UInt64,
            _ => throw new ArgumentException(name)
        };
        var method = new MethodDefinition("Convert", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(Signature(target), [Signature(source)]));
        owner.Methods.Add(method);
        method.CilMethodBody = new CilMethodBody { InitializeLocals = true, ComputeMaxStackOnBuild = true };
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
        NumericConversionEmitter.Emit(method.CilMethodBody,
            new NumericConversion(Type(source), Type(target), (NumericRounding)rounding, fractionalBits));
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        using var stream = new MemoryStream();
        module.Write(stream);
        return Assembly.Load(stream.ToArray()).GetType("Tests.Numeric")!.GetMethod("Convert")!;
    }

    [TestCase("Int32")]
    [TestCase("UInt32")]
    [TestCase("Int64")]
    [TestCase("UInt64")]
    public void ExecutedIlSaturatesAndRoundsAtBoundaries(string target)
    {
        var unsigned = target.StartsWith("U", StringComparison.Ordinal);
        var bits = target.EndsWith("64", StringComparison.Ordinal) ? 64 : 32;
        var upper = Math.Pow(2, bits - (unsigned ? 0 : 1));
        var values = new[] { double.NaN, double.NegativeInfinity, double.PositiveInfinity, -0.0, 0.0,
            -3.75, -3.5, -2.5, -2.1, -1.5, -0.9, -0.5, -0.1, 0.1, 0.5, 0.9, 1.5, 2.1, 2.5, 3.5, 3.75,
            Math.BitDecrement(upper), upper, Math.BitIncrement(upper), -upper,
            Math.BitIncrement(-upper), Math.BitDecrement(-upper), upper - 0.5, upper - 0.25,
            -upper + 0.5, -upper + 0.25, double.Epsilon, -double.Epsilon };
        var random = new Random(1701);
        values = values.Concat(Enumerable.Range(0, 300).Select(_ => (random.NextDouble() - 0.5) * Math.Pow(2, random.Next(0, 80)))).ToArray();
        for (var mode = 0; mode <= 4; mode++)
        {
            var convert = Compile("Double", target, mode);
            foreach (var value in values)
                Assert.That(convert.Invoke(null, [value]), Is.EqualTo(Reference(value, target, mode)), $"{target} mode={mode} value={value:R}");
        }
    }

    private static object Reference(double value, string target, int rounding)
    {
        value = double.IsNaN(value) ? 0 : rounding switch
        {
            0 => Math.Truncate(value), 1 => Math.Floor(value), 2 => Math.Ceiling(value),
            3 => Math.Round(value, MidpointRounding.ToEven), 4 => Math.Round(value, MidpointRounding.AwayFromZero),
            _ => throw new ArgumentException()
        };
        // Explicit object casts keep C# from promoting the switch arms to a common numeric type.
        return target switch
        {
            "Int32" => (object)(value >= 2147483648.0 ? int.MaxValue : value <= int.MinValue ? int.MinValue : (int)value),
            "UInt32" => (object)(value >= 4294967296.0 ? uint.MaxValue : value <= 0 ? 0u : (uint)value),
            "Int64" => (object)(value >= 9223372036854775808.0 ? long.MaxValue : value <= long.MinValue ? long.MinValue : (long)value),
            "UInt64" => (object)(value >= 18446744073709551616.0 ? ulong.MaxValue : value <= 0 ? 0UL : (ulong)value),
            _ => throw new ArgumentException(target)
        };
    }

    [TestCase("Int32", 8)]
    [TestCase("UInt32", 32)]
    [TestCase("Int64", 32)]
    [TestCase("UInt64", 64)]
    public void FixedPointScalingPrecedesIntegerRounding(string target, int fraction)
    {
        var convert = Compile("Single", target, fractionalBits: fraction);
        foreach (var value in new[] { float.NaN, float.NegativeInfinity, float.PositiveInfinity, -1.5f, 0f, 0.5f, 1f, 1.5f })
            Assert.That(convert.Invoke(null, [value]), Is.EqualTo(Reference((double)value * Math.Pow(2, fraction), target, 0)));
    }

    [TestCase("Single")]
    [TestCase("Double")]
    public void IntegerInputsRetainSignednessAndWidth(string target)
    {
        var signed32 = Compile("Int32", target);
        var unsigned32 = Compile("UInt32", target);
        var signed64 = Compile("Int64", target);
        var unsigned64 = Compile("UInt64", target);
        foreach (var number in new[] { 0UL, 1UL, uint.MaxValue, (1UL << 63) + (1UL << 39) + 1, ulong.MaxValue })
        {
            Assert.That(signed32.Invoke(null, [unchecked((int)number)]), Is.EqualTo(target == "Single" ? (object)(float)unchecked((int)number) : (double)unchecked((int)number)));
            Assert.That(unsigned32.Invoke(null, [unchecked((uint)number)]), Is.EqualTo(target == "Single" ? (object)(float)unchecked((uint)number) : (double)unchecked((uint)number)));
            Assert.That(signed64.Invoke(null, [unchecked((long)number)]), Is.EqualTo(target == "Single" ? (object)(float)unchecked((long)number) : (double)unchecked((long)number)));
            Assert.That(unsigned64.Invoke(null, [number]), Is.EqualTo(target == "Single" ? (object)(float)number : (double)number));
        }
    }

    [Test]
    public void FloatingPrecisionAndFixedPointOutputAreExplicit()
    {
        var narrow = Compile("Double", "Single");
        foreach (var value in new[] { -0.0, double.NaN, double.MaxValue, 1.00000007 })
            Assert.That(BitConverter.SingleToInt32Bits((float)narrow.Invoke(null, [value])!), Is.EqualTo(BitConverter.SingleToInt32Bits((float)value)));
        var fixedPoint = Compile("Int32", "Single", fractionalBits: 8);
        Assert.That(fixedPoint.Invoke(null, [384]), Is.EqualTo(1.5f));
    }

    [Test]
    public void FullIlGeneratorPreservesConvertedIndexAndArrayWrite()
    {
        var single = _app.SystemTypes.SystemSingleType;
        var integer = _app.SystemTypes.SystemInt32Type;
        var arrayType = new SzArrayTypeAnalysisContext(integer);
        var source = new LocalVariable("value", new Register(null, "V0"), single);
        var array = new LocalVariable("array", new Register(null, "X0"), arrayType);
        var index = new LocalVariable("index", new Register(null, "X1"));
        var caller = new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType, "Write", _app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [single, arrayType])
        {
            Locals = [index], ParameterLocals = [source, array], AnalysisWarnings = [],
            ControlFlowGraph = new ISILControlFlowGraph([
                new(0, OpCode.ConvertNumeric, index, source, new NumericConversion(single, integer)),
                new(1, OpCode.Move, new ArrayAccess(array, index), new Immediate(7)), new(2, OpCode.Return)])
        };
        LocalVariables.ResolveTypesAndFields(caller);
        SsaSimplifier.Run(caller);
        Simplifier.Simplify(caller);
        var module = new ModuleDefinition("Index" + Guid.NewGuid().ToString("N") + ".dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var core = ModuleDefinition.FromFile(typeof(int).Assembly.Location);
        foreach (var context in new[] { single, integer })
            context.PutExtraData("AsmResolverType", core.TopLevelTypes.Single(t => t.Namespace == "System" && t.Name == context.Name));
        new AssemblyDefinition(module.Name!, new Version(1, 0)).Modules.Add(module);
        var owner = new TypeDefinition("Tests", "Index", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var generated = new MethodDefinition("Write", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.Single, module.CorLibTypeFactory.Int32.MakeSzArrayType()]));
        generated.ParameterDefinitions.Add(new ParameterDefinition(1, "value", (AsmResolver.PE.DotNet.Metadata.Tables.ParameterAttributes)0));
        generated.ParameterDefinitions.Add(new ParameterDefinition(2, "array", (AsmResolver.PE.DotNet.Metadata.Tables.ParameterAttributes)0));
        owner.Methods.Add(generated);
        IlGenerator.GenerateIl(caller, generated);
        generated.CilMethodBody!.ComputeMaxStackOnBuild = true;
        using var stream = new MemoryStream();
        module.Write(stream);
        var execute = Assembly.Load(stream.ToArray()).GetType("Tests.Index")!.GetMethod("Write")!;
        var values = new int[3];
        execute.Invoke(null, [1.9f, values]);
        Assert.That(values, Is.EqualTo(new[] { 0, 7, 0 }));
        execute.Invoke(null, [float.NaN, values]);
        Assert.That(values, Is.EqualTo(new[] { 7, 7, 0 }));
    }
}
