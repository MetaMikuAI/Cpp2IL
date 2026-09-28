using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A homogeneous floating-point aggregate (a Color, a Vector3) travels in V0..Vn, one member each. A call
/// only resolved after lifting takes such an argument as its first register, and a call returning one
/// leaves its members there, where the call's clobbering only gave them new versions without a value.
/// Along straight-line code:
/// <list type="bullet">
/// <item>until the next call, a read of those registers after a call returning an aggregate is its member;</item>
/// <item>an argument of the aggregate's type whose registers all hold the members of one value, in order
/// (a field, a local, or a call's result), is that value (<c>image.color = GetColor()</c>).</item>
/// </list>
/// Runs in SSA, once calls are resolved.
/// </summary>
public static class HfaArgumentRecovery
{
    private readonly record struct Container(LocalVariable Owner, IReadOnlyList<FieldAnalysisContext> Path);

    public static bool Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not InstructionSets.NewArmV8InstructionSet || method.ControlFlowGraph is not { } graph)
            return false;
        var definitions = graph.Instructions.Where(i => i.Destination is LocalVariable).GroupBy(i => (LocalVariable)i.Destination!)
            .ToDictionary(g => g.Key, g => g.Count() == 1 ? g.Single() : null);
        foreach (var parameter in method.ParameterLocals)
            definitions[parameter] = null;

        var changed = false;
        var visited = new HashSet<Block>();
        // Straight-line chains, each from its first block.
        foreach (var start in graph.Blocks.Where(b => b.Predecessors is not [{ Successors: [_] }]))
        {
            var seen = new List<Instruction>();
            for (var block = start; block != null && visited.Add(block);)
            {
                foreach (var instruction in block.Instructions)
                {
                    changed |= Rewrite(instruction, seen, definitions);
                    seen.Add(instruction);
                }
                block = block.Successors is [var next] && next.Predecessors is [_] ? next : null;
            }
        }
        return changed;
    }

    private static bool Rewrite(Instruction instruction, List<Instruction> seen, Dictionary<LocalVariable, Instruction?> definitions)
    {
        var changed = false;
        var target = instruction.IsCall ? instruction.Operands[0] as MethodAnalysisContext : null;
        var argumentBase = instruction.OpCode == OpCode.Call ? 2 : 1;
        for (var position = 0; position < instruction.Operands.Count; position++)
        {
            if (instruction.Operands[position] is not LocalVariable read || read == instruction.Destination
                || Register(read) is not { } register || instruction.IsCall && position < argumentBase)
                continue;

            var parameter = target == null ? -1 : position - argumentBase - (target.IsStatic ? 0 : 1);
            if (target != null && register == 0 && parameter >= 0 && parameter < target.Parameters.Count
                && Arm64CallingConventionResolver.FloatingAggregateFields(target.Parameters[parameter].ParameterType) is { Length: > 0 } members)
            {
                // A whole argument: every register must hold the next member of one value.
                if (Whole(read, members, seen, definitions) is { } value)
                {
                    instruction.SetOperand(position, value);
                    changed = true;
                }
                continue;
            }

            // A member read of the latest aggregate result, where the register has no value of its own.
            if (!definitions.ContainsKey(read) && LatestCall(seen) is { } call && Result(call) is ({ } result, { } fields) && register < fields.Length)
            {
                instruction.SetOperand(position, new FieldReference(fields[register], result, fields[register].Offset));
                changed = true;
            }
        }
        return changed;
    }

    private static IOperand? Whole(LocalVariable first, FieldAnalysisContext[] members, List<Instruction> seen, Dictionary<LocalVariable, Instruction?> definitions)
    {
        Container? container = null;
        for (var k = 0; k < members.Length; k++)
        {
            // The value register k holds at the call: the read itself, or its latest definition since the last call.
            var source = k == 0 ? Source(first, members[0], seen, definitions) : Source(k, members[k], seen);
            if (source is not { } found || container is { } known && !Same(known, found))
                return null;
            container ??= found;
        }
        var (owner, path) = container!.Value;
        return path.Count == 0 ? owner : new FieldReference(path[^1], owner, path[^1].Offset) { ContainingFields = path.Take(path.Count - 1).ToList() };
    }

    // What a register's value is a member of: a read of that member of a value, or the latest call's
    // aggregate result for a register with no value of its own.
    private static Container? Source(LocalVariable read, FieldAnalysisContext member, List<Instruction> seen, Dictionary<LocalVariable, Instruction?> definitions)
    {
        if (!definitions.TryGetValue(read, out var definition))
            return LatestCall(seen) is { } call && Result(call) is ({ } result, { } fields) && fields.Contains(member) ? new Container(result, []) : null;
        return Piece(definition, member);
    }

    private static Container? Source(int register, FieldAnalysisContext member, List<Instruction> seen)
    {
        for (var i = seen.Count - 1; i >= 0; i--)
        {
            var instruction = seen[i];
            if (instruction.IsCall)
                return Result(instruction) is ({ } result, { } fields) && fields.Contains(member) ? new Container(result, []) : null;
            if (instruction.Destination is LocalVariable local && Register(local) == register)
                return Piece(instruction, member);
        }
        return null;
    }

    // A read of the member of some value: the value is the container.
    private static Container? Piece(Instruction? definition, FieldAnalysisContext member)
        => definition is { OpCode: OpCode.Move, Operands: [_, FieldReference { IsStatic: false } piece] } && piece.Field == member
            ? new Container(piece.Local, piece.ContainingFields)
            : null;

    private static Instruction? LatestCall(List<Instruction> seen) => seen.LastOrDefault(i => i.IsCall);

    // The aggregate a call returns in the floating-point registers, and its members.
    private static (LocalVariable Result, FieldAnalysisContext[] Fields)? Result(Instruction call)
        => call is { OpCode: OpCode.Call, Operands: [_, LocalVariable { Register.Name: var name, Type: { } type } result, ..] }
           && name.StartsWith("hfa_ret_") && Arm64CallingConventionResolver.FloatingAggregateFields(type) is { Length: > 0 } fields
            ? (result, fields)
            : null;

    private static int? Register(LocalVariable local)
        => local.Register.Name is ['V', .. var digits] && int.TryParse(digits, out var number) ? number : null;

    private static bool Same(Container left, Container right)
        => left.Owner == right.Owner && left.Path.SequenceEqual(right.Path);
}
