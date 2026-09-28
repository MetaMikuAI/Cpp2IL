using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Native code clears an embedded struct, such as an async state machine's awaiter on resuming
/// (<c>this.&lt;&gt;u__1 = default</c>), one member at a time: <c>&lt;&gt;u__1.task.result = null;
/// &lt;&gt;u__1.task.token = 0; &lt;&gt;u__1.task.source = null</c>. Those name members the caller cannot
/// access. A run of zero stores that together clear every member of one field, nothing else in between,
/// is that field being cleared: store the zero to the whole field, which the IL generator emits as initobj.
/// </summary>
public static class MemberwiseZeroStoreMerging
{
    private const int MaxDepth = 4;

    public static bool Run(MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var changed = false;
        foreach (var block in method.ControlFlowGraph!.Blocks)
        {
            var runs = new Dictionary<(LocalVariable Owner, FieldAnalysisContext Field), List<(Instruction Store, List<string> Leaves)>>();
            foreach (var instruction in block.Instructions)
            {
                if (instruction.OpCode == OpCode.Nop)
                    continue;
                if (instruction is { OpCode: OpCode.Move, Operands: [FieldReference { IsNested: true, IsStatic: false } member, Immediate { Value: 0 }] }
                    && Cleared(member, pointerSize) is { } leaves)
                {
                    var key = (member.Local, member.ContainingFields[0]);
                    if (!runs.TryGetValue(key, out var run))
                        runs[key] = run = [];
                    run.Add((instruction, leaves));
                    continue;
                }
                changed |= Flush(runs, pointerSize);
            }
            changed |= Flush(runs, pointerSize);
        }
        return changed;
    }

    private static bool Flush(Dictionary<(LocalVariable Owner, FieldAnalysisContext Field), List<(Instruction Store, List<string> Leaves)>> runs, int pointerSize)
    {
        var changed = false;
        foreach (var ((owner, field), run) in runs)
        {
            var cleared = run.SelectMany(s => s.Leaves).ToList();
            var all = Leaves(field.FieldType, "", 0).ToList();
            var size = TypeSizes.UnboxedSize(field.FieldType, pointerSize);
            if (cleared.Count != all.Count || !cleared.ToHashSet().SetEquals(all) || size <= 0)
                continue;

            run[0].Store.SetOperands(new FieldReference(field, owner, field.Offset) { AccessSize = (int)size }, new Immediate(0));
            foreach (var (store, _) in run.Skip(1))
            {
                store.OpCode = OpCode.Nop;
                store.SetOperands();
            }
            changed = true;
        }
        runs.Clear();
        return changed;
    }

    // The leaf members of the outermost field a zero store clears, as paths below that field; null if it may
    // clear only part of a member.
    private static List<string>? Cleared(FieldReference member, int pointerSize)
    {
        if (!IsAggregate(member.ContainingFields[0].FieldType))
            return null;
        var path = string.Concat(member.ContainingFields.Skip(1).Append(member.Field).Select(f => "." + f.Name));
        var type = member.Field.FieldType;
        if (IsAggregate(type) && TypeSizes.UnboxedSize(type, pointerSize) is var size && (size <= 0 || member.AccessSize < size))
            return null;
        return Leaves(type, path, member.ContainingFields.Count).ToList();
    }

    private static IEnumerable<string> Leaves(TypeAnalysisContext type, string path, int depth)
    {
        var (definition, arguments) = type is GenericInstanceTypeAnalysisContext generic
            ? (generic.GenericType, generic.GenericArguments)
            : (type, (IReadOnlyList<TypeAnalysisContext>)[]);
        var fields = IsAggregate(type) && depth < MaxDepth ? definition.Fields.Where(f => !f.IsStatic).ToList() : [];
        if (fields.Count == 0)
        {
            yield return path;
            yield break;
        }
        foreach (var field in fields)
        {
            var fieldType = arguments.Count == 0 ? field.FieldType : GenericInstantiation.Instantiate(field.FieldType, arguments, []);
            foreach (var leaf in Leaves(fieldType, path + "." + field.Name, depth + 1))
                yield return leaf;
        }
    }

    private static bool IsAggregate(TypeAnalysisContext type)
        => type is { IsValueType: true, IsEnumType: false } && type.Type is Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE or Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST;
}
