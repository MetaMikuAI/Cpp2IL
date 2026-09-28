using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A call returning a homogeneous floating-point aggregate (a Color, a Vector3) hands its members back in
/// V0..Vn, which the call's result aggregate stands for. Code right after it reads those registers, most
/// often passing them straight on as an argument of the same type (<c>image.color = GetColor()</c>), but
/// they only hold the new versions the call's clobbering gave them, which have no value. Until the next
/// call, such a read is the result's member; a whole argument of the aggregate's type is the result.
/// Runs in SSA, once calls are resolved.
/// </summary>
public static class HfaArgumentRecovery
{
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
            (LocalVariable Result, FieldAnalysisContext[] Fields)? state = null;
            for (var block = start; block != null && visited.Add(block);)
            {
                foreach (var instruction in block.Instructions)
                {
                    if (state is ({ } result, { } fields))
                        changed |= Rewrite(instruction, result, fields, definitions);
                    if (!instruction.IsCall)
                        continue;
                    state = instruction is { OpCode: OpCode.Call, Operands: [_, LocalVariable { Register.Name: var name, Type: { } type } aggregate, ..] }
                            && name.StartsWith("hfa_ret_") && Arm64CallingConventionResolver.FloatingAggregateFields(type) is { Length: > 0 } members
                        ? (aggregate, members)
                        : null;
                }
                // On into a block only this one reaches.
                block = block.Successors is [var next] && next.Predecessors is [_] ? next : null;
            }
        }
        return changed;
    }

    private static bool CopiesMember(Instruction? definition, LocalVariable result, FieldAnalysisContext member)
        => definition is { OpCode: OpCode.Move, Operands: [_, FieldReference { IsNested: false } read] } && read.Local == result && read.Field == member;

    private static bool Rewrite(Instruction instruction, LocalVariable result, FieldAnalysisContext[] fields, Dictionary<LocalVariable, Instruction?> definitions)
    {
        var changed = false;
        var target = instruction.IsCall ? instruction.Operands[0] as MethodAnalysisContext : null;
        var argumentBase = instruction.OpCode == OpCode.Call ? 2 : 1;
        var destination = instruction.Destination;
        for (var position = 0; position < instruction.Operands.Count; position++)
        {
            if (instruction.Operands[position] is not LocalVariable { Register.Name: var name } read || read == destination
                || name.Length < 2 || name[0] != 'V' || !int.TryParse(name[1..], out var register)
                || register >= fields.Length || instruction.IsCall && position < argumentBase)
                continue;
            // The register holds the result's member: only the call's clobbering version, or a copy of the member.
            var undefined = !definitions.TryGetValue(read, out var definition);
            if (!undefined && !CopiesMember(definition, result, fields[register]))
                continue;

            // A whole argument of the result's type is the result.
            var parameter = target == null ? -1 : position - argumentBase - (target.IsStatic ? 0 : 1);
            if (target != null && parameter >= 0 && parameter < target.Parameters.Count
                && target.Parameters[parameter].ParameterType.FullName == result.Type!.FullName)
            {
                if (register != 0)
                    continue;
                instruction.SetOperand(position, result);
            }
            else if (undefined)
                instruction.SetOperand(position, new FieldReference(fields[register], result, fields[register].Offset));
            else
                continue;
            changed = true;
        }
        return changed;
    }
}
