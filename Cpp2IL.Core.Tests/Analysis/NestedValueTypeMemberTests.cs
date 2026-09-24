using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NestedValueTypeMemberTests
{
    // Offsets are relative to a Bounds field: m_Center (Vector3) at 0, m_Extents (Vector3) at 0xC.
    [TestCase(0x10, 4, true, "m_Extents", "y")]
    [TestCase(0x14, 4, true, "m_Extents", "z")]
    [TestCase(0x4, 4, false, "m_Center", "y")]
    [TestCase(0x10, 4, false, "m_Extents", "y")]
    [TestCase(0xC, 4, true, "m_Extents", "x")]
    [TestCase(0xC, 4, false, "m_Extents", "x")]
    [TestCase(0x10, 8, false, null, null)]
    public void ResolvesMembersSeveralValueTypesDeep(int relative, int width, bool store, string? containing, string? member)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var bounds = app.AllTypes.Single(t => t.FullName == "UnityEngine.Bounds");
        var owner = app.AllTypes.Single(t => t.FullName == "UnityEngine.Object");
        var field = owner.Fields.Single(f => f.Name == "m_CachedPtr");
        field.FieldType = bounds;

        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), owner);
        var value = new LocalVariable("value", new Register(null, "value"), app.SystemTypes.SystemSingleType);
        var memory = new MemoryOperand(receiver, addend: field.Offset + relative, accessSize: width);
        var access = store
            ? new Instruction(0, OpCode.Move, memory, value)
            : new Instruction(0, OpCode.Move, value, memory);
        var method = new InjectedMethodAnalysisContext(owner, "Access", app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Static | System.Reflection.MethodAttributes.Public, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([access, new(1, OpCode.Return)]),
            Locals = [receiver, value], ParameterLocals = []
        };

        MetadataResolver.ResolveFieldOffsets(method);

        var operand = access.Operands[store ? 0 : 1];
        if (member == null)
        {
            Assert.That(operand, Is.InstanceOf<MemoryOperand>(), "An access wider than the member must not resolve to it");
            return;
        }

        var reference = (FieldReference)operand;
        Assert.That(reference.Field.Name, Is.EqualTo(member));
        Assert.That(reference.Field.FieldType.FullName, Is.EqualTo("System.Single"));
        Assert.That(reference.ContainingFields.Select(f => f.Name), Is.EqualTo(new[] { field.Name, containing }));
    }
}
