using System;
using System.Collections.Generic;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class IntegerArithmeticTypeTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [TestCase(OpCode.Add, "Int32")]
    [TestCase(OpCode.Subtract, "Int32")]
    [TestCase(OpCode.Multiply, "Int32")]
    [TestCase(OpCode.Add, "UInt32")]
    [TestCase(OpCode.Subtract, "Int64")]
    [TestCase(OpCode.Multiply, "UInt64")]
    public void SameTypedIntegersTypeTheirResult(OpCode opcode, string type)
    {
        var result = Propagate(opcode, Local(type), Local(type));
        Assert.That(result.Type, Is.SameAs(Type(type)));
    }

    [TestCase("Byte")]
    [TestCase("SByte")]
    [TestCase("Int16")]
    [TestCase("UInt16")]
    [TestCase("Char")]
    public void NarrowIntegersArePromoted(string type)
    {
        Assert.That(Propagate(OpCode.Add, Local(type), Local(type)).Type, Is.SameAs(Type("Int32")));
    }

    [TestCase("Int32", 1L)]
    [TestCase("Int32", -1L)]
    [TestCase("UInt32", 4294967295L)]
    [TestCase("Int64", 2147483648L)]
    [TestCase("UInt64", 1L)]
    public void RepresentableLiteralPreservesKnownType(string type, long value)
    {
        Assert.That(Propagate(OpCode.Add, Local(type), new Immediate(value)).Type, Is.SameAs(Type(type)));
        Assert.That(Propagate(OpCode.Subtract, new Immediate(value), Local(type)).Type, Is.SameAs(Type(type)));
    }

    [TestCase("Int32", 2147483648L)]
    [TestCase("UInt32", -1L)]
    [TestCase("UInt32", 4294967296L)]
    [TestCase("UInt64", -1L)]
    public void OutOfRangeLiteralDoesNotGuessAWidth(string type, long value)
    {
        Assert.That(Propagate(OpCode.Add, Local(type), new Immediate(value)).Type, Is.Null);
    }

    [TestCase("IntPtr")]
    [TestCase("UIntPtr")]
    [TestCase("Object")]
    [TestCase("Boolean")]
    public void NonIntegerOperandIsNotInferredAsInteger(string type)
    {
        Assert.That(Propagate(OpCode.Add, Local("Int32"), Local(type)).Type, Is.Null);
        Assert.That(Propagate(OpCode.Add, Local(type), new Immediate(1)).Type, Is.Null);
    }

    [Test]
    public void UnknownOperandAndMixedWidthsAreNotGuessed()
    {
        Assert.That(Propagate(OpCode.Add, Local("Int32"), new LocalVariable("unknown", new Register(null, "unknown"))).Type, Is.Null);
        Assert.That(Propagate(OpCode.Add, Local("Int32"), Local("Int64")).Type, Is.Null);
        Assert.That(Propagate(OpCode.Add, Local("Int32"), Local("UInt32")).Type, Is.Null);
        Assert.That(Propagate(OpCode.Add, new Immediate(1), new Immediate(2)).Type, Is.Null);
    }

    [Test]
    public void ExistingDestinationTypeIsPreserved()
    {
        Assert.That(Propagate(OpCode.Add, Local("Int32"), new Immediate(1), Type("Int64")).Type, Is.SameAs(Type("Int64")));
    }

    [TestCase("Byte", "Int32")]
    [TestCase("SByte", "Int32")]
    [TestCase("Int16", "Int32")]
    [TestCase("UInt16", "Int32")]
    [TestCase("Int32", "Int32")]
    [TestCase("UInt32", "UInt32")]
    [TestCase("Int64", "Int64")]
    [TestCase("UInt64", "UInt64")]
    public void EnumArithmeticUsesUnderlyingIntegerWithoutRetypingEnum(string underlying, string promoted)
    {
        var enumType = new InjectedTypeAnalysisContext(Type("Object").DeclaringAssembly,
            "Tests", "State", Type("Enum"), TypeAttributes.Public)
        {
            OverrideEnumUnderlyingType = Type(underlying),
        };
        var state = new LocalVariable("state", new Register(null, "state"), enumType);
        var biased = Propagate(OpCode.Subtract, state, new Immediate(1));
        Assert.That(biased.Type, Is.SameAs(Type(promoted)));
        Assert.That(Propagate(OpCode.Add, biased, new Immediate(2)).Type, Is.SameAs(Type(promoted)));
        Assert.That(Propagate(OpCode.Subtract, state, state).Type, Is.SameAs(Type(promoted)));
        Assert.That(state.Type, Is.SameAs(enumType));
        Assert.That(Propagate(OpCode.Subtract, state, new LocalVariable("unknown", new Register(null, "unknown"))).Type, Is.Null);
        Assert.That(Propagate(OpCode.Subtract, state, new Immediate(1), Type("Object")).Type, Is.SameAs(Type("Object")));
    }

    [TestCase(OpCode.ShiftLeft)]
    [TestCase(OpCode.ShiftRight)]
    public void ShiftCountDoesNotTypeUnknownValue(OpCode opcode)
    {
        Assert.That(Propagate(opcode, new Immediate(1), Local("Int32")).Type, Is.Null);
        Assert.That(Propagate(opcode, new LocalVariable("unknown", new Register(null, "unknown")), Local("Int32")).Type, Is.Null);
    }

    [TestCase("Byte")]
    [TestCase("SByte")]
    [TestCase("Int16")]
    [TestCase("UInt16")]
    [TestCase("Int32")]
    [TestCase("UInt32")]
    [TestCase("Int64")]
    [TestCase("UInt64")]
    public void EnumBitwiseResultsMatchUnderlyingIntegerWidth(string underlying)
    {
        var enumType = new InjectedTypeAnalysisContext(Type("Object").DeclaringAssembly,
            "Tests", "Flags", Type("Enum"), TypeAttributes.Public)
        {
            OverrideEnumUnderlyingType = Type(underlying),
        };
        var flags = new LocalVariable("flags", new Register(null, "flags"), enumType);
        foreach (var opcode in new[] { OpCode.And, OpCode.Or, OpCode.Xor })
        {
            var expected = Propagate(opcode, Local(underlying), new Immediate(255)).Type;
            Assert.That(expected, Is.Not.Null);
            Assert.That(Propagate(opcode, flags, new Immediate(255)).Type, Is.SameAs(expected));
            Assert.That(Propagate(opcode, new Immediate(255), flags).Type, Is.SameAs(expected));
            Assert.That(Propagate(opcode, flags, flags).Type, Is.SameAs(expected));
            Assert.That(Propagate(opcode, flags, new Immediate(255), Type("Object")).Type, Is.SameAs(Type("Object")));
            Assert.That(Propagate(opcode, flags, new LocalVariable("unknown", new Register(null, "unknown"))).Type, Is.Null);
            if (underlying == "Int32")
                foreach (var mask in new[] { 0xFFFFFFFFL, 0xFFFFFFFEL, -4294967296L })
                {
                    Assert.That(Propagate(opcode, flags, new Immediate(mask)).Type, Is.Null, "a wide mask can pack native struct words");
                    Assert.That(Propagate(opcode, new Immediate(mask), flags).Type, Is.Null);
                }
        }
        Assert.That(flags.Type, Is.SameAs(enumType));
    }

    [TestCase("UInt32")]
    [TestCase("UInt64")]
    [TestCase("Int64")]
    public void ShiftResultPreservesValueTypeNotCountType(string type)
    {
        Assert.That(Propagate(OpCode.ShiftLeft, Local(type), Local("Int32")).Type, Is.SameAs(Type(type)));
        Assert.That(Propagate(OpCode.ShiftRight, Local(type), Local("Int32")).Type, Is.SameAs(Type(type)));
    }

    [TestCase(OpCode.And)]
    [TestCase(OpCode.Or)]
    [TestCase(OpCode.Xor)]
    public void BooleanBitwiseLiteralsRequireAKnownBoolean(OpCode opcode)
    {
        var flag = Local("Boolean");
        foreach (var value in new long[] { 0, 1 })
        {
            var literal = new Immediate(value);
            Assert.That(Propagate(opcode, flag, literal).Type, Is.SameAs(Type("Boolean")));
            Assert.That(Propagate(opcode, literal, flag).Type, Is.SameAs(Type("Boolean")));
            Assert.That(Propagate(opcode, literal, new LocalVariable("unknown", new Register(null, "unknown"))).Type, Is.Null);
            Assert.That(Propagate(opcode, literal, new Immediate(1)).Type, Is.Null);
            Assert.That(Propagate(opcode, Local("Int32"), literal).Type, Is.SameAs(Type("Int32")));
            Assert.That(Propagate(opcode, flag, literal, Type("Object")).Type, Is.SameAs(Type("Object")));
        }
        foreach (var value in new long[] { -1, 2, 255 })
        {
            Assert.That(Propagate(opcode, flag, new Immediate(value)).Type, Is.Null);
            Assert.That(Propagate(opcode, new Immediate(value), flag).Type, Is.Null);
        }
        Assert.That(Propagate(opcode, flag, Local("Boolean")).Type, Is.SameAs(Type("Boolean")));
        Assert.That(flag.Type, Is.SameAs(Type("Boolean")));
    }

    [Test]
    public void BooleanLiteralInferenceWaitsForStorageAndIndexTypes()
    {
        var flag = Local("Boolean");
        Assert.That(Propagate(OpCode.Xor, flag, new Immediate(1), late: false).Type, Is.Null);
        Assert.That(Propagate(OpCode.Xor, flag, new Immediate(1), Type("IntPtr")).Type, Is.SameAs(Type("IntPtr")));
        Assert.That(Propagate(OpCode.Xor, flag, new Immediate(1), Type("Int32")).Type, Is.SameAs(Type("Int32")));
    }

    private static TypeAnalysisContext Type(string name) => Cpp2IlApi.CurrentAppContext!.AssembliesByName["mscorlib"].GetTypeByFullName("System." + name)!;
    private static LocalVariable Local(string type) => new(Guid.NewGuid().ToString(), new Register(null, Guid.NewGuid().ToString()), Type(type));

    private static LocalVariable Propagate(OpCode opcode, IOperand left, IOperand right, TypeAnalysisContext? resultType = null, bool late = true)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "IntegerArithmetic",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        var result = new LocalVariable("result", new Register(null, "result"), resultType);
        method.ControlFlowGraph = new ISILControlFlowGraph([new Instruction(0, opcode, result, left, right), new Instruction(1, OpCode.Return)]);
        typeof(LocalVariables).GetMethod("PropagateTypesOnce", BindingFlags.Static | BindingFlags.NonPublic)!.Invoke(null, [method]);
        if (late)
            LocalVariables.PropagateKnownTypes(method);
        return result;
    }
}
