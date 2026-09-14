using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Recover calls and tail calls through a delegate's invoke_impl as managed Invoke calls.
public static class DelegateInvokeRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        var instructions = method.ControlFlowGraph!.Blocks.SelectMany(block => block.Instructions).ToList();

        // Il2CppObject is two pointers (klass, monitor), then method_ptr, then invoke_impl.
        var invokeImplOffset = method.AppContext.Binary.PointerSizeBytes * 3;

        var candidates = new List<(Instruction Call, LocalVariable Receiver, MethodAnalysisContext Invoke, Block Block)>();
        foreach (var block in method.ControlFlowGraph.Blocks)
        foreach (var instruction in block.Instructions.ToList())
        {
            if (instruction.OpCode is not (OpCode.IndirectCall or OpCode.IndirectJump))
                continue;

            if (GetInvokeImplReceiver(instruction, instructions, invokeImplOffset) is not { Type: { } delegateType } delegateLocal)
                continue;

            // Constructed types have no Methods of their own (and metadata-backed instances
            // need not have a BaseType). Resolve on the definition, then substitute its args.
            var definition = delegateType is GenericInstanceTypeAnalysisContext generic ? generic.GenericType : delegateType;
            if (!definition.IsDelegate
                || definition.Methods.FirstOrDefault(m => m.Name == "Invoke" && !m.IsStatic) is not { } invoke)
                continue;
            if (delegateType is GenericInstanceTypeAnalysisContext instance)
                invoke = new ConcreteGenericMethodAnalysisContext(invoke, instance.GenericArguments.ToArray(), []);

            if (CanRewrite(instruction, invoke, method))
                candidates.Add((instruction, delegateLocal, invoke, block));
        }

        // The IL fallback for an unresolved IndirectJump only emits a diagnostic, not a
        // terminator. Mixing it with newly explicit returns can make block layout fall off
        // the end of the IL body. Until that fallback is fixed, recover tails atomically;
        // in particular, leave shared/phi dispatch targets we cannot prove untouched.
        var allTailsResolved = candidates.Count(c => c.Call.OpCode == OpCode.IndirectJump)
            == instructions.Count(i => i.OpCode == OpCode.IndirectJump);
        foreach (var (call, receiver, invoke, block) in candidates)
            if (call.OpCode != OpCode.IndirectJump || allTailsResolved)
                RewriteAsInvoke(call, receiver, invoke, method, block);
    }

    private static LocalVariable? GetInvokeImplReceiver(Instruction call, List<Instruction> instructions, int invokeImplOffset)
    {
        if (call.Operands.Count == 0)
            return null;

        var source = call.Operands[0];
        if (source is LocalVariable target)
        {
            var definition = instructions.FirstOrDefault(i => ReferenceEquals(i.Destination, target));
            if (definition is not { OpCode: OpCode.Move, Operands: [_, var loaded] })
                return null;
            source = loaded;
        }

        if (source is MemoryOperand { Base: LocalVariable receiver, Index: null, Scale: 0 } memory
            && memory.Addend == invokeImplOffset)
            return receiver;

        // This pass runs after ResolveTypesAndFields: the load may already be a Delegate
        // field reference, including a scalar read of the embedded IntPtr.m_value.
        if (source is not FieldReference reference || reference.Offset != invokeImplOffset)
            return null;

        var field = reference.ContainingField ?? reference.Field;
        if (field is not { Name: "invoke_impl", IsStatic: false, DeclaringType.FullName: "System.Delegate" }
            || field.Offset != invokeImplOffset)
            return null;

        if (reference.IsNested && reference.Field is not
            { Name: "m_value", Offset: 0, IsStatic: false, DeclaringType.FullName: "System.IntPtr" })
            return null;

        return reference.Local;
    }

    private static bool CanRewrite(Instruction call, MethodAnalysisContext invoke, MethodAnalysisContext caller)
    {
        if (invoke.AppContext.InstructionSet.CallingConventionResolver is not { } callingConventions
            || !callingConventions.HasRawArgumentLayout(call, invoke.AppContext))
            return false;

        // A raw register snapshot cannot recover stack arguments or an aggregate return buffer.
        // Leave those cases unresolved rather than silently dropping managed arguments.
        return !callingConventions.ReturnsViaHiddenBuffer(invoke)
            && !callingConventions.ResolveForManaged(invoke).Any(operand => operand is StackOffset)
            && !(call.OpCode == OpCode.IndirectJump && !caller.IsVoid && invoke.IsVoid);
    }

    private static void RewriteAsInvoke(Instruction call, LocalVariable delegateLocal, MethodAnalysisContext invoke,
        MethodAnalysisContext caller, Block block)
    {
        var callingConventions = invoke.AppContext.InstructionSet.CallingConventionResolver!;
        var isTailCall = call.OpCode == OpCode.IndirectJump;
        if (isTailCall)
        {
            // IndirectJump has no SSA destination: operand 1 is a stale register use, not a
            // result. Allocate a new typed local, including the FP return register when needed.
            var operands = new List<IOperand> { invoke };
            if (!invoke.IsVoid)
            {
                var result = new LocalVariable("delegateTailCallResult", callingConventions.ReturnRegister(invoke), invoke.ReturnType);
                caller.Locals.Add(result);
                operands.Add(result);
            }
            operands.AddRange(call.Operands.Skip(2));
            call.SetOperands(operands);
        }
        else
        {
            if (invoke.IsVoid)
                call.RemoveOperandAt(1);
            else if (call.ImplicitDefinition is { } returnDefinition
                     && returnDefinition.Number == callingConventions.ReturnRegister(invoke).Number
                     && caller.Locals.FirstOrDefault(local => local.Register == returnDefinition) is { } result)
                call.SetOperand(1, result);

            call.SetOperand(0, invoke);
        }

        call.OpCode = invoke.IsVoid ? OpCode.CallVoid : OpCode.Call;
        // Remapping validates raw register identities. Replacing X0 with a delegate held in
        // another register first would defeat that validation and leave FP arguments unmapped.
        callingConventions.RemapRawArguments(call, invoke);
        call.SetOperand(invoke.IsVoid ? 1 : 2, delegateLocal);

        if (isTailCall)
        {
            var returnOperands = !caller.IsVoid && !invoke.IsVoid
                ? new List<IOperand> { call.Operands[1] }
                : [];
            block.AddInstruction(new Instruction(-1, OpCode.Return, returnOperands));
            block.CalculateBlockType();
        }
    }
}
