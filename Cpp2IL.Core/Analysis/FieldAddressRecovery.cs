using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Recover an interior address only where the call signature proves it is a managed byref.
public static class FieldAddressRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        var definitions = new Dictionary<LocalVariable, Instruction?>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
            if (instruction.Destination is LocalVariable local)
                definitions[local] = definitions.ContainsKey(local) ? null : instruction;

        foreach (var call in method.ControlFlowGraph.Instructions)
        {
            if (!call.IsCall || call.Operands[0] is not MethodAnalysisContext target)
                continue;
            var first = call.OpCode == OpCode.CallVoid ? 1 : 2;
            for (var i = first; i < call.Operands.Count; i++)
            {
                var parameter = i - first - (target.IsStatic ? 0 : 1);
                var expected = !target.IsStatic && i == first ? target.DeclaringType
                    : parameter >= 0 && parameter < target.Parameters.Count
                        && target.Parameters[parameter].ParameterType is ByRefTypeAnalysisContext byRef ? byRef.ElementType : null;
                if (expected == null || !target.IsStatic && i == first && !expected.IsValueType
                    || call.Operands[i] is not LocalVariable address
                    || !definitions.TryGetValue(address, out var definition)
                    || definition is not { OpCode: OpCode.Add, Operands: [_, var left, var right] })
                    continue;
                if (left is Immediate) (left, right) = (right, left);
                // After SSA destruction, other locals can be reassigned between address creation
                // and use. An unmodified implicit receiver remains the same object throughout.
                var receiver = left switch
                {
                    LocalVariable { IsThis: true } thisLocal => thisLocal,
                    AddressOf { Target: LocalVariable storage } when method.StackAggregates.ContainsKey(storage.Register.Number) => storage,
                    _ => null
                };
                if (receiver?.Type is not { } owner
                    || definitions.ContainsKey(receiver) || right is not Immediate { Value: >= 0 and <= int.MaxValue } offset
                    || owner is GenericInstanceTypeAnalysisContext || owner.GenericParameters.Count != 0)
                    continue;
                var fields = owner.Fields.Where(f => !f.IsStatic && f.Offset == offset.Value).ToList();
                if (fields is not [{ } field] || field.FieldType.FullName != expected.FullName
                    || field.FieldType.DeclaringAssembly != expected.DeclaringAssembly)
                    continue;
                call.SetOperand(i, new AddressOf(new FieldReference(field, receiver, (int)offset.Value)));
            }
        }
    }
}
