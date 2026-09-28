using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// The constructors the C# compiler generates for its own classes do nothing but initialize, so IL2CPP inlines
/// them: a closure's <c>&lt;&gt;c__DisplayClass</c> is allocated and then only <c>object..ctor</c> runs, and an
/// iterator's <c>&lt;M&gt;d__N(int state)</c> becomes <c>object..ctor</c> followed by the stores of <c>&lt;&gt;1__state</c> and
/// <c>&lt;&gt;l__initialThreadId = Environment.CurrentManagedThreadId</c>. Allocated that way the object reads as
/// <c>(T)new object()</c>, which the decompiler cannot fold into a lambda or a <c>yield</c> method. Call the type's
/// own constructor again, taking over the stores it performs.
/// </summary>
public static class CompilerGeneratedConstructorRecovery
{
    public static bool Run(MethodAnalysisContext method)
    {
        var changed = false;
        foreach (var block in method.ControlFlowGraph!.Blocks)
        {
            var list = block.Instructions;
            for (var i = 0; i < list.Count; i++)
            {
                if (list[i] is not { OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: ".ctor" } baseConstructor, LocalVariable created] } call
                    || baseConstructor.DeclaringType?.FullName != "System.Object"
                    || created.IsThis || created.Type is not { IsValueType: false } type || !type.Name.StartsWith("<") || type is ReferencedTypeAnalysisContext)
                    continue;
                var constructors = type.Methods.Where(m => m is { Name: ".ctor", IsStatic: false }).ToList();
                if (constructors.FirstOrDefault(c => c.Parameters.Count == 0) is { } parameterless)
                {
                    call.SetOperands(parameterless, created);
                    changed = true;
                    continue;
                }
                // An iterator's: <>1__state from the argument, <>l__initialThreadId from the current thread.
                if (constructors is not [{ Parameters: [{ ParameterType.FullName: "System.Int32" }] } iterator]
                    || type.Fields.FirstOrDefault(f => f.Name == "<>1__state") is not { } stateField
                    || type.Fields.FirstOrDefault(f => f.Name == "<>l__initialThreadId") is not { } threadField)
                    continue;
                // The stores follow the call, into the next blocks when a call ends one (a straight chain only).
                var following = list.Skip(i + 1).ToList();
                for (var chain = block; chain.Successors is [var only] && only.Predecessors is [var from] && from == chain && following.Count < 16; chain = only)
                    following.AddRange(only.Instructions);
                Instruction? stateStore = null, threadStore = null, threadRead = null;
                LocalVariable? threadId = null;
                foreach (var next in following.Take(16))
                {
                    if (next is { OpCode: OpCode.Move, Operands: [FieldReference { Field: var f, Local: var owner }, Immediate] } && owner == created && f == stateField)
                        stateStore = next;
                    else if (next is { OpCode: OpCode.Call, Operands: [MethodAnalysisContext { Name: "get_CurrentManagedThreadId" }, LocalVariable read] })
                        (threadRead, threadId) = (next, read);
                    else if (next is { OpCode: OpCode.Move, Operands: [FieldReference { Field: var g, Local: var holder }, LocalVariable stored] } && holder == created
                             && g == threadField && stored == threadId
                             && !method.ControlFlowGraph.Instructions.Any(ins => ins != next && DeadCodeEliminator.UsedLocals(ins).Contains(stored)))
                        threadStore = next;
                    else if (next.IsCall || next.OpCode is OpCode.Return or OpCode.ConditionalJump || next.Destination is FieldReference { Local: var other } && other == created && next != stateStore)
                        break;
                    if (stateStore != null && threadStore != null)
                        break;
                }
                if (stateStore == null || threadStore == null || threadRead == null)
                    continue;
                // The 32-bit field is written from a W register, so -2 reads as its unsigned form.
                call.SetOperands(iterator, created, new Immediate(unchecked((int)((Immediate)stateStore.Operands[1]).Value)));
                foreach (var absorbed in new[] { stateStore, threadStore, threadRead })
                {
                    absorbed.OpCode = OpCode.Nop;
                    absorbed.SetOperands();
                }
                changed = true;
            }
        }
        return changed;
    }
}
