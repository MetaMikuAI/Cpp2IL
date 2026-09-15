using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

public static class ArrayElementClassRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        // Il2CppClass::element_class in the 64-bit v29/v31 layout.
        if (method.AppContext.Binary.PointerSizeBytes != 8 || method.AppContext.MetadataVersion is < 29 or >= 32)
            return;
        var definitions = method.ControlFlowGraph!.Instructions
            .Where(i => i.Destination is LocalVariable || i is { OpCode: OpCode.NewArr, Operands: [LocalVariable, _, _] })
            .GroupBy(i => (LocalVariable)(i.OpCode == OpCode.NewArr ? i.Operands[0] : i.Destination!)).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());

        IOperand Value(IOperand operand)
        {
            var seen = new HashSet<LocalVariable>();
            while (operand is LocalVariable local && seen.Add(local) && definitions.TryGetValue(local, out var definition)
                && definition is { OpCode: OpCode.Move, Operands: [_, var source] })
                operand = source;
            return operand;
        }

        SzArrayTypeAnalysisContext? ExactClass(IOperand operand)
        {
            operand = Value(operand);
            if (operand is RuntimeClassTypeAnalysisContext klass)
                return klass.RepresentedType as SzArrayTypeAnalysisContext;
            if (operand is SzArrayTypeAnalysisContext arrayType)
                return arrayType;
            if (operand is not MemoryOperand { Base: { } array, Index: null, Addend: 0, Scale: 0 }
                || Value(array) is not LocalVariable allocated || !definitions.TryGetValue(allocated, out var allocation))
                return null;
            // A declared object[] could hold a string[]. Only a proven allocation
            // establishes the actual element class, not the inferred local type.
            if (allocation is { OpCode: OpCode.NewArr, Operands: [_, var type, _] })
                return Value(type) as SzArrayTypeAnalysisContext;
            if (allocation is { OpCode: OpCode.Call, Operands: [StringLiteral { Value:
                "SzArrayNew" or "il2cpp_vm_array_new_specific" or "il2cpp_array_new_specific" }, _, var allocatedType, _, ..] })
                return Value(allocatedType) as SzArrayTypeAnalysisContext;
            return null;
        }

        foreach (var instruction in method.ControlFlowGraph.Instructions)
            if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable result,
                    MemoryOperand { Base: { } klass, Index: null, Scale: 0, Addend: 0x40 }] }
                && ExactClass(klass) is { ElementType: var element })
            {
                var runtimeClass = new RuntimeClassTypeAnalysisContext(element, element.DeclaringAssembly);
                instruction.SetOperand(1, runtimeClass);
                result.Type = runtimeClass;
            }
    }
}
