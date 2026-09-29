using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A UniTask a call returns comes back in registers, and native code stores those registers straight into
/// the task it builds for the next call: <c>task.source = OnExiting(); task.token = X1</c>. Only the first
/// register is modelled as the call's result, so the token stored is whatever the register held before the
/// call. Those stores, straight after the call and writing every member, are the returned task itself:
/// <c>task = OnExiting()</c>. Runs out of SSA.
/// </summary>
public static class UniTaskReturnRecovery
{
    public static bool Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var changed = false;
        foreach (var block in graph.Blocks)
        {
            for (var i = 0; i < block.Instructions.Count; i++)
            {
                if (block.Instructions[i] is not { OpCode: OpCode.Call, Operands: [MethodAnalysisContext callee, LocalVariable returned, ..] } call
                    || !IsTask(callee.ReturnType))
                    continue;
                // The source store, with nothing but nops since the call.
                var next = i + 1;
                while (next < block.Instructions.Count && block.Instructions[next].OpCode == OpCode.Nop)
                    next++;
                if (next >= block.Instructions.Count
                    || block.Instructions[next] is not { OpCode: OpCode.Move, Operands: [FieldReference { IsNested: false, Field.Name: "source" } source, LocalVariable stored] }
                    || stored != returned || source.Local is not { IsThis: false, Type: { } taskType } task
                    || taskType.FullName != callee.ReturnType.FullName || task == returned)
                    continue;

                // Then every other member, each once, before anything else.
                var members = Definition(taskType).Fields.Where(f => !f.IsStatic).Select(f => f.Name).ToHashSet();
                var stores = new List<Instruction> { block.Instructions[next] };
                var written = new HashSet<string> { "source" };
                for (var j = next + 1; j < block.Instructions.Count && written.Count < members.Count; j++)
                {
                    var member = block.Instructions[j];
                    if (member.OpCode == OpCode.Nop)
                        continue;
                    if (member is not { OpCode: OpCode.Move, Operands: [FieldReference { IsNested: false } field, _] } || field.Local != task
                        || !members.Contains(field.Field.Name) || !written.Add(field.Field.Name))
                        break;
                    stores.Add(member);
                }
                if (written.Count != members.Count || !members.SetEquals(written)
                    // The first register means nothing else on its own.
                    || graph.Instructions.Count(x => DeadCodeEliminator.UsedLocals(x).Contains(returned)) != 1)
                    continue;

                call.SetOperands([callee, task, .. call.Operands.Skip(2)]);
                foreach (var store in stores)
                {
                    store.OpCode = OpCode.Nop;
                    store.SetOperands();
                }
                changed = true;
            }
        }
        return changed;
    }

    private static TypeAnalysisContext Definition(TypeAnalysisContext type) => (type as GenericInstanceTypeAnalysisContext)?.GenericType ?? type;

    private static bool IsTask(TypeAnalysisContext? type)
        => type != null && Definition(type).FullName is "Cysharp.Threading.Tasks.UniTask" or "Cysharp.Threading.Tasks.UniTask`1";
}
