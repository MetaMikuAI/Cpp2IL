using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A register holding a whole small struct (a Vector2 loaded as 8 bytes) whose low part is moved into a
/// scalar reads the struct's first member: <c>fmov s0, w8</c> after <c>ldr x8, [this, #field]</c> is
/// <c>field.x</c>. Such a move is left typed struct-to-scalar, which reads as the whole value being stored
/// into the scalar (<c>sizeDelta.x = (float)vector</c>), so make it read the member.
/// </summary>
public static class AggregatePieceRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction is not { OpCode: OpCode.Move, Operands: [var destination, LocalVariable { Type: { } sourceType } source] })
                continue;

            var destinationType = destination switch
            {
                FieldReference field => field.Field.FieldType,
                LocalVariable local => local.Type,
                _ => null,
            };
            if (destinationType is null || !IsScalar(destinationType)
                || sourceType is GenericInstanceTypeAnalysisContext
                || sourceType is not { IsValueType: true, IsEnumType: false } || IsScalar(sourceType)
                || sourceType.FullName == destinationType.FullName
                || GenericInstanceFieldLayout.FindFieldAtUnboxedOffset(sourceType, 0) is not { } first
                || first.FieldType.FullName != destinationType.FullName)
                continue;

            instruction.SetOperand(1, new FieldReference(first, source, 0));
        }
    }

    private static bool IsScalar(TypeAnalysisContext type) => type.FullName is "System.Single" or "System.Double"
        or "System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64" or "System.Int16" or "System.UInt16"
        or "System.Byte" or "System.SByte" or "System.Boolean" or "System.Char";
}
