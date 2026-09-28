using System.Collections.Generic;
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
        var instructions = method.ControlFlowGraph!.Instructions;
        foreach (var instruction in instructions)
            RecoverMaskedOrShiftedMember(instruction, instructions);

        foreach (var instruction in instructions)
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

    // A small struct held whole in a register (a bool? passed in one) whose member is picked out by masking
    // the low bytes (value & 0xFF is hasValue) or shifting the last member down (option >> 32) reads that member.
    private static void RecoverMaskedOrShiftedMember(Instruction instruction, List<Instruction> instructions)
    {
        if (instruction is not { OpCode: OpCode.And or OpCode.ShiftRight, Operands: [LocalVariable destination, LocalVariable { Type: { } type } source, Immediate amount, ..] }
            || type is not { IsValueType: true, IsEnumType: false } || IsScalar(type)
            || GenericInstanceFieldLayout.ValueTypeSizeAndAlignment(type) is not ({ } size and <= 8, _)
            || GenericInstanceFieldLayout.ComputeLayout(type) is not { Complete: true, Slots: var slots })
            return;

        var slot = instruction.OpCode == OpCode.And
            ? slots.FirstOrDefault(s => s.Offset == 0 && s.Size < 8 && amount.Value == (1L << (int)(8 * s.Size)) - 1)
            : slots.FirstOrDefault(s => amount.Value == 8 * s.Offset && s.Offset > 0 && s.Offset + s.Size == size);
        // Into a value of the struct itself, a mask truncates the struct rather than reading a member.
        if (slot == null || !IsScalar(slot.Field.FieldType) && slot.Field.FieldType.IsValueType
            || destination.Type is { } destinationType && destinationType != type.AppContext.SystemTypes.SystemObjectType && !IsScalar(destinationType))
            return;

        instruction.OpCode = OpCode.Move;
        instruction.SetOperands(destination, new FieldReference(slot.Field, source, (int)slot.Offset));
        // The untyped temporary the bits went into is the member now.
        if ((destination.Type is null || destination.Type == type.AppContext.SystemTypes.SystemObjectType)
            && instructions.Count(i => i.Destination == destination) == 1)
            destination.Type = slot.Field.FieldType;
    }

    private static bool IsScalar(TypeAnalysisContext type) => type.FullName is "System.Single" or "System.Double"
        or "System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64" or "System.Int16" or "System.UInt16"
        or "System.Byte" or "System.SByte" or "System.Boolean" or "System.Char";
}
