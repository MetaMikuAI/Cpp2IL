using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A constructor runs its field initializers, then the base constructor. Native code computes an
/// initializer's value into a register first, which the decompiler keeps as a local; with statements
/// before it the base call cannot be written in C# and comes out as <c>base..ctor()</c>. The base
/// constructors of object and Unity's object types observe nothing, so run such a call first instead.
/// </summary>
public static class BaseConstructorHoisting
{
    public static bool Run(MethodAnalysisContext method)
    {
        // Compiler-generated closures and anonymous types keep the shape the decompiler recognises them by.
        if (method is not { Name: ".ctor", IsStatic: false } || method.ControlFlowGraph is not { } graph
            || method.DeclaringType is not { } owner || IsCompilerGenerated(owner))
            return false;
        // The first block with code: the synthetic entry block is not necessarily emitted first.
        var entry = graph.EntryBlock;
        while (entry.Instructions.All(i => i.OpCode is OpCode.Nop or OpCode.Jump) && entry.Successors is [var only] && only.Predecessors is [_])
            entry = only;
        // The base call on the straight line from there.
        for (var block = entry; block != null; block = block.Successors is [var next] && next.Predecessors is [_] ? next : null)
        {
            var call = block.Instructions.FirstOrDefault(i => i is { OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: ".ctor" } target, LocalVariable { IsThis: true }] }
                                                              && Unobservable(target));
            if (call == null)
            {
                if (block.Instructions.Any(PassesThis))
                    return false;
                continue;
            }
            // Nothing before it hands this to other code, which could see the base object unconstructed.
            if (block.Instructions.TakeWhile(i => i != call).Any(PassesThis)
                || block == entry && entry.Instructions.TakeWhile(i => i != call).All(i => i.OpCode == OpCode.Nop))
                return false;
            block.Instructions.Remove(call);
            entry.Instructions.Insert(entry.Instructions.FindIndex(i => i.OpCode != OpCode.Nop) is >= 0 and var first ? first : 0, call);
            return true;
        }
        return false;
    }

    private static bool IsCompilerGenerated(TypeAnalysisContext type)
    {
        for (TypeAnalysisContext? current = type; current != null; current = current.DeclaringType)
            if (current.Name.StartsWith('<'))
                return true;
        return false;
    }

    private static bool PassesThis(Instruction instruction)
        => instruction.IsCall && instruction.Operands.Skip(1).Any(o => o is LocalVariable { IsThis: true });

    private static bool Unobservable(MethodAnalysisContext constructor)
        => constructor.Parameters.Count == 0 && constructor.DeclaringType?.FullName is "System.Object" or "UnityEngine.MonoBehaviour" or "UnityEngine.Behaviour"
            or "UnityEngine.Component" or "UnityEngine.Object" or "UnityEngine.ScriptableObject";
}
