using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Fully shared generic code asks whether a type argument is a value type by testing the top bit of its
/// class's byval_arg bit field word (<c>klass-&gt;byval_arg.valuetype</c>): <c>[klass + 0x28] &amp; 0x80000000</c>.
/// That is <c>typeof(T).IsValueType</c>.
/// </summary>
public static class SharedValueTypeTestRecovery
{
    // Il2CppClass::byval_arg's bit field word in the 64-bit v29-v31 layout, and its valuetype bit.
    private const long ByvalArgBitsOffset = 0x28;
    private const long ValueTypeBit = 0x80000000;
    // Il2CppClass::stack_slot_size
    private const long StackSlotSizeOffset = 0xFC;

    public static bool Run(MethodAnalysisContext method)
    {
        if (method.AppContext.Binary.PointerSizeBytes != 8 || method.AppContext.MetadataVersion is < 29 or >= 32
            || method.ControlFlowGraph is not { } graph
            || method.AppContext.SystemTypes.SystemTypeType.Methods.FirstOrDefault(m => m is { Name: "get_IsValueType", IsStatic: false, Parameters.Count: 0 }) is not { } isValueType)
            return false;

        var uses = new Dictionary<LocalVariable, List<Instruction>>();
        foreach (var instruction in graph.Instructions)
            foreach (var used in DeadCodeEliminator.UsedLocals(instruction))
            {
                if (!uses.TryGetValue(used, out var list))
                    uses[used] = list = [];
                list.Add(instruction);
            }

        var changed = false;
        // The size a type argument takes where shared code keeps a value of it (its stack_slot_size, which
        // sizes the buffers holding one): Unsafe.SizeOf<T>().
        var sizeOf = method.AppContext.GetAssemblyByName("System.Runtime.CompilerServices.Unsafe")
            ?.GetTypeByFullName("System.Runtime.CompilerServices.Unsafe")
            ?.Methods.FirstOrDefault(m => m is { Name: "SizeOf", IsStatic: true, Parameters.Count: 0 } && m.GenericParameters.Count == 1);
        var types = method.AppContext.SystemTypes;
        if (sizeOf != null)
            foreach (var block in graph.Blocks)
            foreach (var load in block.Instructions.ToList())
            {
                if (load is not { OpCode: OpCode.Move, Operands: [LocalVariable size, MemoryOperand
                    {
                        Base: LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: GenericParameterTypeAnalysisContext typeArgument } },
                        Index: null, Scale: 0, Addend: StackSlotSizeOffset
                    }] })
                    continue;
                // The 32-bit field goes on in 64-bit size arithmetic (rounding a buffer up), so widen the Int32.
                var name = $"sizeOf{method.Locals.Count}";
                var narrow = new LocalVariable(name, new Register(null, name), types.SystemInt32Type);
                method.Locals.Add(narrow);
                load.OpCode = OpCode.Call;
                load.SetOperands(sizeOf.MakeGenericInstanceMethod(typeArgument), narrow);
                block.Instructions.Insert(block.Instructions.IndexOf(load) + 1, new Instruction(load.Index, OpCode.ZeroExtend, size, narrow,
                    new Immediate(32)) { NativeAddress = load.NativeAddress });
                size.Type = types.SystemInt64Type;
                changed = true;
            }

        foreach (var load in graph.Instructions.ToList())
        {
            if (load is not { OpCode: OpCode.Move, Operands: [LocalVariable bits, MemoryOperand
                {
                    Base: LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: GenericParameterTypeAnalysisContext typeArgument } },
                    Index: null, Scale: 0, Addend: ByvalArgBitsOffset
                }] }
                || !uses.TryGetValue(bits, out var bitUses) || bitUses.Count == 0
                || !bitUses.All(IsValueTypeBitMask))
                continue;

            load.OpCode = OpCode.Call;
            load.SetOperands(isValueType, bits, typeArgument);
            bits.Type = method.AppContext.SystemTypes.SystemBooleanType;
            // The masked bit, or the word being negative, is set exactly when the type is a value type, which the
            // flag now says; the word not being negative is the opposite.
            foreach (var use in bitUses)
            {
                var result = (LocalVariable)use.Operands[0];
                if (use.OpCode == OpCode.CheckGreaterOrEqual)
                {
                    use.OpCode = OpCode.CheckEqual;
                    use.SetOperands(result, bits, new Immediate(0));
                }
                else
                {
                    use.OpCode = OpCode.Move;
                    use.SetOperands(result, bits);
                }
                result.Type = bits.Type;
            }
            changed = true;
        }
        return changed;

        bool IsValueTypeBitMask(Instruction use) => use is { OpCode: OpCode.And, Operands: [LocalVariable, var left, var right] }
            && (left is Immediate { Value: ValueTypeBit } || right is Immediate { Value: ValueTypeBit })
            // A signed test of the word against zero reads its top bit: word < 0, word >= 0.
            || use is { OpCode: OpCode.CheckLess or OpCode.CheckGreaterOrEqual, Operands: [LocalVariable, LocalVariable, Immediate { Value: 0 }] };
    }
}
