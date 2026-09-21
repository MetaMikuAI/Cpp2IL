using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Fixes the compare-a-flag-against-zero pairs the we get for every conditional: <c>bool != 0</c>
/// is the bool itself, and <c>bool == 0</c> is its negation.
/// </summary>
public static class BooleanFlagSimplifier
{
    // Run after storage/index typing: only genuinely boolean results may discard
    // the integer representation used by native bitwise operations.
    internal static void SimplifyLiteralOperations(MethodAnalysisContext method)
    {
        var booleanType = method.AppContext.SystemTypes.SystemBooleanType;
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction is not { OpCode: OpCode.And or OpCode.Or or OpCode.Xor,
                    Operands: [LocalVariable destination, var left, var right] }
                || destination.Type != booleanType)
                continue;
            if (left is Immediate)
                (left, right) = (right, left);
            if (left is not LocalVariable { Type: { } type } || type != booleanType
                || right is not Immediate { Value: 0 or 1 } literal)
                continue;

            var opcode = instruction.OpCode;
            var constantResult = opcode == OpCode.And && literal.Value == 0
                || opcode == OpCode.Or && literal.Value == 1;
            instruction.OpCode = opcode == OpCode.Xor && literal.Value == 1 ? OpCode.Not : OpCode.Move;
            instruction.SetOperands(destination, constantResult ? literal : left);
        }
    }

    public static void Run(MethodAnalysisContext method)
    {
        var booleanType = method.AppContext.SystemTypes.SystemBooleanType;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode is not (OpCode.CheckEqual or OpCode.CheckNotEqual) || instruction.Operands.Count < 3)
                continue;

            if (!IsZeroConstant(instruction.Operands[2]))
                continue;

            if (instruction.Operands[1] is not LocalVariable { Type: { } type } || type != booleanType)
                continue;

            instruction.OpCode = instruction.OpCode == OpCode.CheckNotEqual ? OpCode.Move : OpCode.Not;
            instruction.SetOperands(instruction.Operands[0], instruction.Operands[1]);
        }
    }

    private static bool IsZeroConstant(IOperand operand) => operand is Immediate { Value: 0 };
}
