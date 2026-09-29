using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Native code can spill a struct's registers into a stack slot nothing reads again, such as a UniTask
/// returned in registers whose pieces are stored but never used (<c>uniTask.token = token;
/// uniTask.source = source</c>). Those stores name private members for nothing: drop every member store
/// to a stack aggregate that is never read, has its address taken or is used whole. Likewise stores into the
/// hidden return buffer of a method whose every return hands back the value itself.
/// </summary>
public static class UnreadAggregateStoreElimination
{
    public static bool Run(MethodAnalysisContext method)
    {
        var instructions = method.ControlFlowGraph!.Instructions;
        var candidates = instructions.Select(Store).OfType<LocalVariable>()
            .Where(l => method.StackAggregates.ContainsKey(l.Register.Number) && !l.IsThis && !method.ParameterLocals.Contains(l))
            .ToHashSet();
        // Any other appearance of the aggregate reads it.
        foreach (var instruction in instructions)
        {
            if (Store(instruction) is { } stored && candidates.Contains(stored)
                && instruction.Operands.Skip(1).All(o => !Mentions(o, stored)))
                continue;
            candidates.RemoveWhere(c => instruction.Operands.Any(o => Mentions(o, c)));
        }
        // The hidden return buffer is written for nothing when every return hands back its value.
        if (!method.IsVoid && instructions.Where(i => i.OpCode == OpCode.Return).All(i => i.Operands.Count == 1))
        {
            var buffer = instructions.Select(Store).OfType<LocalVariable>().FirstOrDefault(l => l.Name == "returnBuffer" && method.ParameterLocals.Contains(l) == false);
            if (buffer != null && instructions.All(i => Store(i) == buffer ? i.Operands.Skip(1).All(o => !Mentions(o, buffer)) : !i.Operands.Any(o => Mentions(o, buffer))))
                candidates.Add(buffer);
        }
        if (candidates.Count == 0)
            return false;
        foreach (var instruction in instructions.Where(i => Store(i) is { } stored && candidates.Contains(stored)))
        {
            instruction.OpCode = OpCode.Nop;
            instruction.SetOperands();
        }
        return true;
    }

    private static LocalVariable? Store(Instruction instruction)
        => instruction is { OpCode: OpCode.Move, Operands: [FieldReference { IsStatic: false } member, _] } ? member.Local : null;

    private static bool Mentions(IOperand operand, LocalVariable local) => operand switch
    {
        LocalVariable l => l == local,
        FieldReference f => f.Local == local,
        AddressOf { Target: var target } => Mentions(target, local),
        MemoryOperand m => m.Base == local || m.Index == local,
        ArrayAccess a => a.Array == local || a.Index == local,
        ArrayLength l => l.Array == local,
        _ => false,
    };
}
