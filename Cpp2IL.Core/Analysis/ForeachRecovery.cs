using System;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Restore the exception-protected region corresponding to a lowered foreach loop.
/// </summary>
public static class ForeachRecovery
{
    public static void Run(MethodDefinition method)
    {
        var body = method.CilMethodBody;
        if (body is null || body.ExceptionHandlers.Count != 0)
            return;

        var instructions = body.Instructions;
        for (var moveNextIndex = 0; moveNextIndex < instructions.Count; moveNextIndex++)
        {
            if (instructions[moveNextIndex] is not { OpCode.Code: CilCode.Call, Operand: IMethodDescriptor moveNext }
                || !string.Equals(moveNext.Name, "MoveNext", StringComparison.Ordinal)
                || moveNextIndex == 0
                || instructions[moveNextIndex - 1] is not { OpCode.Code: CilCode.Ldloca, Operand: CilLocalVariable enumerator })
                continue;

            if (!TryFindEnumeratorStore(instructions, moveNextIndex, enumerator, out var enumeratorStore)
                || !TryFindNormalDispose(instructions, moveNextIndex, enumerator, out var disposeLoadIndex)
                || !HasLoopBack(instructions, moveNextIndex, enumerator))
                continue;

            var tryStartIndex = enumeratorStore + 1;
            if (tryStartIndex >= disposeLoadIndex || disposeLoadIndex + 2 >= instructions.Count)
                continue;

            // IL2CPP native exception lowering leaves initobj and Dispose paths outside the main loop.
            // Reusing the same local makes ILSpy treat the enumerator as escaping the using scope,
            // so isolate a local for the canonical foreach shape.
            var foreachEnumerator = new CilLocalVariable(enumerator.VariableType);
            if (!RestoreCurrentAccess(instructions, moveNextIndex, disposeLoadIndex, enumerator, foreachEnumerator))
                continue;

            body.LocalVariables.Add(foreachEnumerator);
            instructions[enumeratorStore].Operand = foreachEnumerator;
            instructions[moveNextIndex - 1].Operand = foreachEnumerator;

            // The lowered IL2CPP CFG calls Dispose explicitly on the normal exit; a managed foreach
            // leaves the protected region and calls Dispose only from finally, so replace the call with leave.
            var continuation = instructions[disposeLoadIndex + 2];
            instructions[disposeLoadIndex].OpCode = CilOpCodes.Leave;
            instructions[disposeLoadIndex].Operand = new CilInstructionLabel(continuation);
            instructions.RemoveAt(disposeLoadIndex + 1);

            // The finally handler must end at an instruction boundary; keep a NOP as an exclusive end marker.
            var factory = method.DeclaringModule!.CorLibTypeFactory;
            var disposable = factory.CorLibScope.CreateTypeReference("System", "IDisposable");
            var dispose = disposable.CreateMemberReference(
                "Dispose", MethodSignature.CreateInstance(factory.Void));
            var handlerStart = instructions.Add(CilOpCodes.Ldloca, foreachEnumerator);
            instructions.Add(CilOpCodes.Constrained, foreachEnumerator.VariableType.ToTypeDefOrRef());
            instructions.Add(CilOpCodes.Callvirt, dispose);
            instructions.Add(CilOpCodes.Endfinally);
            var handlerEnd = instructions.Add(CilOpCodes.Nop);

            body.ExceptionHandlers.Add(new CilExceptionHandler
            {
                HandlerType = CilExceptionHandlerType.Finally,
                TryStart = new CilInstructionLabel(instructions[tryStartIndex]),
                TryEnd = new CilInstructionLabel(continuation),
                HandlerStart = new CilInstructionLabel(handlerStart),
                HandlerEnd = new CilInstructionLabel(handlerEnd),
            });

            return;
        }
    }

    private static bool TryFindEnumeratorStore(CilInstructionCollection instructions, int moveNextIndex,
        CilLocalVariable enumerator, out int storeIndex)
    {
        storeIndex = -1;
        for (var i = moveNextIndex - 2; i >= 0; i--)
        {
            if (instructions[i].OpCode.Code == CilCode.Stloc
                && ReferenceEquals(instructions[i].Operand, enumerator))
            {
                storeIndex = i;
                return instructions[i - 1].OpCode.Code == CilCode.Call
                    && instructions[i - 1].Operand is IMethodDescriptor method
                    && string.Equals(method.Name, "GetEnumerator", StringComparison.Ordinal);
            }

            if (instructions[i].OpCode.Code is CilCode.Ret or CilCode.Throw)
                break;
        }

        return false;
    }

    private static bool TryFindNormalDispose(CilInstructionCollection instructions, int moveNextIndex,
        CilLocalVariable enumerator, out int disposeLoadIndex)
    {
        disposeLoadIndex = -1;

        for (var i = moveNextIndex + 1; i + 1 < instructions.Count; i++)
        {
            if (instructions[i].OpCode.Code != CilCode.Ldloca
                || !ReferenceEquals(instructions[i].Operand, enumerator)
                || instructions[i + 1] is not { OpCode.Code: CilCode.Call, Operand: IMethodDescriptor method }
                || !string.Equals(method.Name, "Dispose", StringComparison.Ordinal))
                continue;

            disposeLoadIndex = i;
            return true;
        }

        return false;
    }

    private static bool HasLoopBack(CilInstructionCollection instructions, int moveNextIndex, CilLocalVariable enumerator)
    {
        var loopEntry = instructions[moveNextIndex - 1];
        return instructions.Any(i => i.OpCode.Code == CilCode.Br
            && i.Operand is CilInstructionLabel { Instruction: var target }
            && ReferenceEquals(target, loopEntry));
    }

    private static bool RestoreCurrentAccess(CilInstructionCollection instructions, int moveNextIndex,
        int disposeLoadIndex, CilLocalVariable enumerator, CilLocalVariable foreachEnumerator)
    {
        var restored = false;
        for (var i = moveNextIndex + 1; i + 1 < disposeLoadIndex; i++)
        {
            if (instructions[i] is not { OpCode.Code: CilCode.Ldloc, Operand: CilLocalVariable loaded }
                || !ReferenceEquals(loaded, enumerator)
                || instructions[i + 1] is not { OpCode.Code: CilCode.Ldfld, Operand: IFieldDescriptor currentField }
                || !string.Equals(currentField.Name, "_current", StringComparison.Ordinal)
                || currentField.Signature?.FieldType is not { } currentType
                || currentField.DeclaringType is not { } declaringType
                || declaringType.ToString()?.Contains("Enumerator", StringComparison.Ordinal) != true)
                continue;

            // Current is the instance getter on a value-type enumerator; native compilation may inline it
            // as _current, so restore the managed pointer call form.
            instructions[i].OpCode = CilOpCodes.Ldloca;
            instructions[i].Operand = foreachEnumerator;
            instructions[i + 1].OpCode = CilOpCodes.Call;
            instructions[i + 1].Operand = new MemberReference(
                declaringType.ToTypeSignature(null).ToTypeDefOrRef(),
                "get_Current",
                MethodSignature.CreateInstance(currentType));
            restored = true;
        }

        return restored;
    }

}
