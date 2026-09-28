using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class InlinedListAddRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    [TestCase("join", true)]
    [TestCase("return", true)]
    [TestCase("splitHead", true)]
    [TestCase("lengthLocal", true)]
    [TestCase("addressStore", true)]
    [TestCase("addressStoreWrongOffset", false)]
    [TestCase("phi", true)]
    [TestCase("phiDiffers", false)]
    [TestCase("otherItem", false)]
    [TestCase("sizeUsedLater", false)]
    [TestCase("foreignList", false)]
    public void InlinedAdd_IsRecoveredOnlyForTheExactShape(string shape, bool recovered)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = app.AllTypes.Single(t => t.FullName == "System.Collections.Generic.List`1");
        if (shape == "foreignList")
        {
            var foreign = new InjectedAssemblyAnalysisContext("Other", app);
            var fake = new InjectedTypeAnalysisContext(foreign, "System.Collections.Generic", "List`1", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
            fake.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0, LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_VAR, System.Reflection.GenericParameterAttributes.None, fake));
            foreach (var name in new[] { "_version", "_size", "_items" })
                fake.Fields.Add(new InjectedFieldAnalysisContext(name, app.SystemTypes.SystemInt32Type, System.Reflection.FieldAttributes.Private, fake));
            fake.Methods.Add(new InjectedMethodAnalysisContext(fake, "AddWithResize", app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Private, [app.SystemTypes.SystemStringType]));
            fake.Methods.Add(new InjectedMethodAnalysisContext(fake, "Add", app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Public, [app.SystemTypes.SystemStringType]));
            owner = fake;
        }
        var instance = new GenericInstanceTypeAnalysisContext(owner, [app.SystemTypes.SystemStringType]);
        FieldReference Field(LocalVariable local, string name)
            => new(new ConcreteGenericFieldAnalysisContext(owner.Fields.Single(f => f.Name == name), instance), local, 0);
        LocalVariable Local(string name, TypeAnalysisContext type) => new(name, new Register(null, name), type);

        var list = Local("list", instance);
        var item = Local("item", app.SystemTypes.SystemStringType);
        var other = Local("other", app.SystemTypes.SystemStringType);
        var version = Local("version", app.SystemTypes.SystemInt32Type);
        var nextVersion = Local("nextVersion", app.SystemTypes.SystemInt32Type);
        var items = Local("items", app.SystemTypes.SystemStringType.MakeSzArrayType());
        var size = Local("size", app.SystemTypes.SystemInt32Type);
        var nextSize = Local("nextSize", app.SystemTypes.SystemInt32Type);
        var full = Local("full", app.SystemTypes.SystemBooleanType);
        var length = Local("length", app.SystemTypes.SystemInt32Type);
        var address = Local("address", app.SystemTypes.SystemInt32Type);
        var scaled = Local("scaled", app.SystemTypes.SystemInt32Type);
        var element = Local("element", app.SystemTypes.SystemInt64Type);
        var elementAddress = Local("elementAddress", app.SystemTypes.SystemInt64Type);
        var resize = new ConcreteGenericMethodAnalysisContext(owner.Methods.Single(m => m.Name == "AddWithResize"), [app.SystemTypes.SystemStringType], []);

        var slowCall = new Instruction(11, OpCode.CallVoid, resize, list, item) { DeclaredArguments = 2 };
        var end = new Instruction(12, OpCode.Return, shape == "sizeUsedLater" ? [nextSize] : []);
        var sizeLoad = new Instruction(4, OpCode.Move, size, Field(list, "_size"));
        List<Instruction> instructions =
        [
            new(0, OpCode.Move, version, Field(list, "_version")),
            new(1, OpCode.Move, items, Field(list, "_items")),
            new(2, OpCode.Add, nextVersion, version, new Immediate(1)),
            new(3, OpCode.Move, Field(list, "_version"), nextVersion),
            .. shape == "splitHead" ? new[] { new Instruction(3, OpCode.Jump, sizeLoad) } : [],
            sizeLoad,
            .. shape == "lengthLocal" ? new[] { new Instruction(5, OpCode.Move, length, new ArrayLength(items)) } : [],
            new(5, OpCode.CheckGreaterOrEqual, full, size, shape == "lengthLocal" ? length : new ArrayLength(items), app.SystemTypes.SystemUInt32Type),
            new(6, OpCode.ConditionalJump, slowCall, full),
            new(7, OpCode.Add, nextSize, size, new Immediate(1)),
            new(8, OpCode.Move, Field(list, "_size"), nextSize),
            .. shape.StartsWith("addressStore")
                ? new Instruction[]
                {
                    new(9, OpCode.ShiftLeft, scaled, size, new Immediate(3)),
                    new(9, OpCode.Add, element, items, scaled),
                    new(9, OpCode.Add, elementAddress, element, new Immediate(shape == "addressStore" ? 32 : 24)),
                    new(9, OpCode.Move, new MemoryOperand(elementAddress), item),
                }
                : [new(9, OpCode.Move, new ArrayAccess(items, size), shape == "otherItem" ? other : item)],
            new(9, OpCode.ShiftLeft, address, size, new Immediate(3)),
            shape == "return" ? new Instruction(10, OpCode.Return) : new Instruction(10, OpCode.Jump, end),
            slowCall,
            end,
        ];
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
        {
            Locals = [list, item, other, version, nextVersion, items, size, nextSize, full, length, address, scaled, element, elementAddress], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph(instructions),
        };

        // As by metadata resolution, before this runs.
        method.ControlFlowGraph.MergeCallBlocks();
        var merged = Local("merged", app.SystemTypes.SystemStringType);
        if (shape is "phi" or "phiDiffers")
        {
            // A loop-carried value at the join, as at a loop header.
            var join = method.ControlFlowGraph.Blocks.Single(b => b.Instructions.Contains(end));
            var inputs = join.Predecessors.Select(p => (IOperand)(shape == "phiDiffers" && p.Instructions.Contains(slowCall) ? other : item)).ToList();
            join.Instructions.Insert(0, new Instruction(12, OpCode.Phi, [merged, .. inputs]));
            end.SetOperands(merged);
        }

        Assert.That(InlinedListAddRecovery.Run(method), Is.EqualTo(recovered));

        var remaining = method.ControlFlowGraph.Blocks.SelectMany(b => b.Instructions).Where(i => i.OpCode != OpCode.Nop).ToList();
        var calls = remaining.Where(i => i.OpCode == OpCode.CallVoid).Select(i => ((MethodAnalysisContext)i.Operands[0]).Name).ToList();
        if (!recovered)
        {
            Assert.That(calls, Is.EqualTo(new[] { "AddWithResize" }));
            return;
        }
        Assert.That(calls, Is.EqualTo(new[] { "Add" }));
        var add = remaining.Single(i => i.OpCode == OpCode.CallVoid);
        Assert.That(add.Operands.Skip(1), Is.EqualTo(new IOperand[] { list, item }));
        Assert.That(((ConcreteGenericMethodAnalysisContext)add.Operands[0]).TypeGenericParameters, Is.EqualTo(new[] { app.SystemTypes.SystemStringType }));
        Assert.That(remaining.Any(i => i.Operands.Any(o => o is FieldReference or ArrayAccess or MemoryOperand)), Is.False, "the inlined body and its loads are gone");
        Assert.That(remaining.Count(i => i.OpCode == OpCode.Return), Is.EqualTo(1));
        foreach (var block in method.ControlFlowGraph.Blocks)
            Assert.That(block.Instructions.Where(i => i.OpCode == OpCode.Phi).All(i => i.Operands.Count == block.Predecessors.Count + 1), "phis stay aligned with predecessors");
        if (shape == "phi")
            Assert.That(remaining.Single(i => i.OpCode == OpCode.Phi).Operands.Skip(1), Is.EqualTo(new IOperand[] { item }));
    }
}

public class InlinedListAddStructRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    [TestCase(true)]
    [TestCase(false)]
    public void StructItem_WrittenMemberwiseOnBothArms_IsRecovered(bool sameValues)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = app.AllTypes.Single(t => t.FullName == "System.Collections.Generic.List`1");
        var vector = app.AllTypes.Single(t => t.FullName == "UnityEngine.Vector2");
        var (x, y) = (vector.Fields.Single(f => f.Name == "x"), vector.Fields.Single(f => f.Name == "y"));
        var instance = new GenericInstanceTypeAnalysisContext(owner, [vector]);
        FieldReference Field(LocalVariable local, string name)
            => new(new ConcreteGenericFieldAnalysisContext(owner.Fields.Single(f => f.Name == name), instance), local, 0);
        LocalVariable Local(string name, TypeAnalysisContext type) => new(name, new Register(null, name), type);

        var list = Local("list", instance);
        var (a, b, c) = (Local("a", app.SystemTypes.SystemSingleType), Local("b", app.SystemTypes.SystemSingleType), Local("c", app.SystemTypes.SystemSingleType));
        var version = Local("version", app.SystemTypes.SystemInt32Type);
        var nextVersion = Local("nextVersion", app.SystemTypes.SystemInt32Type);
        var items = Local("items", vector.MakeSzArrayType());
        var size = Local("size", app.SystemTypes.SystemInt32Type);
        var nextSize = Local("nextSize", app.SystemTypes.SystemInt32Type);
        var full = Local("full", app.SystemTypes.SystemBooleanType);
        var (elementX, elementY) = (Local("elementX", new ByRefTypeAnalysisContext(vector)), Local("elementY", new ByRefTypeAnalysisContext(vector)));
        var built = Local("built", vector);
        var resize = new ConcreteGenericMethodAnalysisContext(owner.Methods.Single(m => m.Name == "AddWithResize"), [vector], []);

        var slowStart = new Instruction(20, OpCode.Move, new FieldReference(x, built, 0), a);
        var end = new Instruction(30, OpCode.Return);
        List<Instruction> instructions =
        [
            new(0, OpCode.Move, version, Field(list, "_version")),
            new(1, OpCode.Move, items, Field(list, "_items")),
            new(2, OpCode.Add, nextVersion, version, new Immediate(1)),
            new(3, OpCode.Move, Field(list, "_version"), nextVersion),
            new(4, OpCode.Move, size, Field(list, "_size")),
            new(5, OpCode.CheckGreaterOrEqual, full, size, new ArrayLength(items), app.SystemTypes.SystemUInt32Type),
            new(6, OpCode.ConditionalJump, slowStart, full),
            new(7, OpCode.Add, nextSize, size, new Immediate(1)),
            new(8, OpCode.Move, Field(list, "_size"), nextSize),
            new(9, OpCode.Move, elementX, new AddressOf(new ArrayAccess(items, size))),
            new(10, OpCode.Move, new FieldReference(x, elementX, 0), a),
            new(11, OpCode.Move, elementY, new AddressOf(new ArrayAccess(items, size))),
            new(12, OpCode.Move, new FieldReference(y, elementY, 4), sameValues ? b : c),
            new(13, OpCode.Jump, end),
            slowStart,
            new(21, OpCode.Move, new FieldReference(y, built, 4), b),
            new(22, OpCode.CallVoid, resize, list, built) { DeclaredArguments = 2 },
            end,
        ];
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
        {
            Locals = [list, a, b, c, version, nextVersion, items, size, nextSize, full, elementX, elementY, built], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph(instructions),
        };
        method.ControlFlowGraph.MergeCallBlocks();

        Assert.That(InlinedListAddRecovery.Run(method), Is.EqualTo(sameValues));
        if (!sameValues)
            return;

        var remaining = method.ControlFlowGraph.Blocks.SelectMany(i => i.Instructions).Where(i => i.OpCode != OpCode.Nop).ToList();
        Assert.That(remaining.Select(i => i.OpCode), Is.EqualTo(new[] { OpCode.Move, OpCode.Move, OpCode.CallVoid, OpCode.Jump, OpCode.Return }));
        Assert.That(remaining.Take(2).Select(i => ((FieldReference)i.Operands[0]).Local), Is.All.EqualTo(built), "the argument is built before the call");
        Assert.That(((MethodAnalysisContext)remaining[2].Operands[0]).Name, Is.EqualTo("Add"));
        Assert.That(remaining[2].Operands.Skip(1), Is.EqualTo(new IOperand[] { list, built }));
    }
}
