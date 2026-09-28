using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Native code storing a struct into a field can write one member of it first, the whole value after:
/// an async method suspending on an awaiter stores <c>&lt;&gt;u__1.task.token = token; &lt;&gt;u__1 = awaiter</c>,
/// keeping the awaiter's token in a register of its own. The whole store overwrites the member, whose
/// store names a private field; drop it when nothing between them can see the field.
/// </summary>
public static class OverwrittenMemberStoreElimination
{
    public static bool Run(MethodAnalysisContext method)
    {
        var changed = false;
        foreach (var block in method.ControlFlowGraph!.Blocks)
        {
            var instructions = block.Instructions;
            for (var i = 0; i < instructions.Count; i++)
            {
                if (instructions[i] is not { OpCode: OpCode.Move, Operands: [FieldReference { IsNested: true, IsStatic: false } member, _] } store)
                    continue;
                var owner = member.Local;
                var field = member.ContainingFields[0];
                for (var j = i + 1; j < instructions.Count; j++)
                {
                    var next = instructions[j];
                    if (next is { OpCode: OpCode.Move, Operands: [FieldReference { IsNested: false, IsStatic: false } whole, var value] }
                        && whole.Local == owner && whole.Field == field && value is LocalVariable or Immediate)
                    {
                        store.OpCode = OpCode.Nop;
                        store.SetOperands();
                        changed = true;
                        break;
                    }
                    if (next.OpCode != OpCode.Nop && (next.IsCall || next.OpCode != OpCode.Move
                            || next.Destination == owner || DeadCodeEliminator.UsedLocals(next).Contains(owner)))
                        break;
                }
            }
        }
        return changed;
    }
}
