using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests;

public class StackFieldAddressRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    [TestCase(OpCode.Or, 4, "value")]
    [TestCase(OpCode.Add, 4, "value")]
    [TestCase(OpCode.Or, 20, null)]
    public void StackStructAddressPlusOffset_IsTheMembersAddress(OpCode opCode, long offset, string? member)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var pairType = app.AllTypes.Single(t => t.FullName == "System.Collections.Generic.KeyValuePair`2");
        var pair = new GenericInstanceTypeAnalysisContext(pairType, [app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemInt32Type]);
        var slot = new LocalVariable("slot", new Register(null, "stack_-90"), pair);
        var address = new LocalVariable("address", new Register(null, "address"), null);
        var form = new Instruction(0, opCode, address, new AddressOf(slot), new Immediate(offset));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, [])
        {
            Locals = [slot, address], ParameterLocals = [],
            ControlFlowGraph = new ISILControlFlowGraph([form, new Instruction(1, OpCode.Return)]),
        };

        Assert.That(StackFieldAddressRecovery.Run(method), Is.EqualTo(member != null));
        if (member == null)
            return;
        Assert.That(form.Operands[1] is AddressOf { Target: FieldReference { Field.Name: var name, Local: var l } } && name == member && l == slot);
        Assert.That(address.Type, Is.TypeOf<ByRefTypeAnalysisContext>());
    }
}
