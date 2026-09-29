using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A store or load through a byref (an out bool) can resolve to a field of an unrelated type at the same
/// offset, of the byref's own type (<c>((TileData*)&amp;isDummy)->_allocate = false</c>), which C# cannot
/// express. Access the referent directly instead.
/// </summary>
public static class ByRefFieldAccessRecovery
{
    // What a byref local, or a parameter declared by reference, refers to.
    private static TypeAnalysisContext? Referent(MethodAnalysisContext method, LocalVariable local)
    {
        if (local.Type is ByRefTypeAnalysisContext { ElementType: var element })
            return element;
        if (!method.ParameterLocals.Contains(local))
            return null;
        var parameter = method.Parameters.FirstOrDefault(p => p.Name == local.Name);
        return parameter?.ParameterType is ByRefTypeAnalysisContext { ElementType: var declared } ? declared : null;
    }

    public static bool Run(MethodAnalysisContext method)
    {
        var changed = false;
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            for (var position = 0; position < instruction.Operands.Count; position++)
            {
                if (instruction.Operands[position] is not FieldReference { IsNested: false, IsStatic: false, Offset: 0, Local: var local, Field: var field }
                    || Referent(method, local) is not { } referent
                    || field.DeclaringType.FullName == referent.FullName || field.FieldType.FullName != referent.FullName)
                    continue;
                // A byref parameter typed otherwise by propagation keeps its declared type.
                if (local.Type is not ByRefTypeAnalysisContext)
                    local.Type = new ByRefTypeAnalysisContext(referent);
                instruction.SetOperand(position, new MemoryOperand(local));
                changed = true;
            }
        }
        return changed;
    }
}
