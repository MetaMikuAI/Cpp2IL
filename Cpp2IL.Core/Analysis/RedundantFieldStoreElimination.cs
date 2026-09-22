using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

internal static class RedundantFieldStoreElimination
{
    internal static void Run(MethodAnalysisContext context)
    {
        // Limit this to private compiler-generated storage. Never cross a block,
        // call, read, address operation, or another memory access.
        foreach (var block in context.ControlFlowGraph!.Blocks)
        {
            Instruction? previous = null;
            foreach (var instruction in block.Instructions)
            {
                if (instruction.OpCode == OpCode.Nop) continue;
                if (instruction is { OpCode: OpCode.Move, Operands: [FieldReference field, Immediate] }
                    && !field.IsNested && !field.Field.IsStatic
                    && field.Field.Visibility == System.Reflection.FieldAttributes.Private
                    && field.Field.FieldType.FullName == "System.Int32"
                    && field.Field.DeclaringType.IsCompilerGeneratedBasedOnCustomAttributes)
                {
                    if (previous is { Operands: [FieldReference old, Immediate] }
                        && old.Field == field.Field && old.Local == field.Local && old.Offset == field.Offset)
                    {
                        previous.OpCode = OpCode.Nop;
                        previous.SetOperands();
                    }
                    previous = instruction;
                }
                else previous = null;
            }
        }
    }
}
