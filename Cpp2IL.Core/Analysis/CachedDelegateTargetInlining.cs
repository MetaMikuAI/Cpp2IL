using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A lambda capturing nothing is a method of the compiler-generated singleton <c>&lt;&gt;c</c>, and its delegate is
/// built as <c>new Func(&lt;&gt;c.&lt;&gt;9, &amp;&lt;M&gt;b__0)</c> with the singleton read straight into the constructor
/// (<c>ldsfld &lt;&gt;9; ldftn; newobj</c>). Read into a local first, the singleton looks like a closure instance
/// to the decompiler, which then keeps it as a variable and cannot fold the cached-delegate initialization
/// (<c>&lt;&gt;9__0 ?? (&lt;&gt;9__0 = ...)</c>) back into the lambda. <c>&lt;&gt;9</c> is initonly and set by the static
/// constructor, so reading it where the delegate is built instead is the same value.
/// </summary>
public static class CachedDelegateTargetInlining
{
    public static void Run(MethodAnalysisContext method)
    {
        var instructions = method.ControlFlowGraph!.Instructions;
        foreach (var load in instructions)
        {
            if (load is not { OpCode: OpCode.Move, Operands: [LocalVariable singleton, FieldReference { IsNested: false, Field: { IsStatic: true, Name: "<>9" } field } read] }
                || field.DeclaringType?.Name != "<>c")
                continue;
            if (instructions.Count(i => ReferenceEquals(i.Destination, singleton)) != 1)
                continue;
            var uses = instructions.Where(i => i != load && DeadCodeEliminator.UsedLocals(i).Contains(singleton)).ToList();
            if (uses is not [{ OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: ".ctor" } constructor, _, var target, ..] } construction]
                || !ReferenceEquals(target, singleton)
                || (constructor.DeclaringType is GenericInstanceTypeAnalysisContext generic ? generic.GenericType : constructor.DeclaringType)?.BaseType?.FullName != "System.MulticastDelegate")
                continue;
            construction.SetOperand(2, read);
            load.OpCode = OpCode.Nop;
            load.SetOperands();
        }
    }
}
