using System.Collections.Generic;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Recovers <c>obj is T</c> / <c>as T</c> checks that il2cpp inlines as a typeHierarchy probe:
/// <code>
///   srcKlass = [obj]; th = [srcKlass + 0xC8]; entry = [th + T.depth*8 - 8]; check = entry == klass(T)
/// </code>
/// The comparison is equivalent to <c>isinst(obj, T) != null</c>, which the IL layer already
/// knows how to emit, so the whole probe collapses to an IsInst plus a null test.
/// </summary>
public static class TypeHierarchyCheckRecovery
{
    private const long TypeHierarchyOffset64 = 0xC8;
    private const long TypeHierarchyDepthOffset64 = 0x12C;
    private const long InterfaceOffsetsOffset64 = 0xB0;
    private const long InterfaceOffsetsCountOffset64 = 0x12A;

    public static void Run(MethodAnalysisContext method)
    {
        if (method.AppContext.Binary.PointerSizeBytes != 8)
            return;

        // Fold [klass + typeHierarchyDepth] to a constant: unlike cctor flags, the depth is fixed
        // at compile time, so both sides of the depth guard collapse and the whole probe dies.
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                // never fold a store target - only loads
                if (instruction.OpCode == OpCode.Move && i == 0 && instruction.Operands[0] is MemoryOperand)
                    continue;

                if (instruction.Operands[i] is not MemoryOperand { Index: null, Scale: 0, Addend: TypeHierarchyDepthOffset64, Base: LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: { } represented } } })
                    continue;

                if (represented.IsInterface)
                    continue;

                var depth = 0L;
                for (var t = represented; t != null; t = t.BaseType)
                    depth++;

                if (depth > 0)
                    instruction.SetOperand(i, new Immediate(depth));
            }
        }

        // Fold [klass + interface_offsets_count] to a constant: the implemented-interface count
        // is metadata-fixed, so interface-scan loop bounds become compile-time constants.
        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                if (instruction.OpCode == OpCode.Move && i == 0 && instruction.Operands[0] is MemoryOperand)
                    continue;

                if (instruction.Operands[i] is MemoryOperand { Index: null, Scale: 0, Addend: InterfaceOffsetsCountOffset64, Base: LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: { Definition: { } interfaceOwner } } } })
                    instruction.SetOperand(i, new Immediate((long)interfaceOwner.InterfaceOffsetsCount));
            }
        }

        // Fold [methodInfo + slot] to the constant vtable slot: for a methodof-loaded MethodInfo
        // the slot is compile-time known, which then lets vtable-indexed dispatch resolve.
        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                if (instruction.OpCode == OpCode.Move && i == 0 && instruction.Operands[0] is MemoryOperand)
                    continue;

                if (instruction.Operands[i] is MemoryOperand { Index: null, Scale: 0, Addend: 0x50, Base: LocalVariable { Type: RuntimeMethodInfoAnalysisContext { RepresentedMethod: { Definition: { } methodDef } } } })
                    instruction.SetOperand(i, new Immediate(methodDef.slot));
            }
        }

        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in method.ControlFlowGraph.Instructions)
            if (instruction.Destination is LocalVariable destination)
                definitions[destination] = instruction;

        // Fold cctor guard loads ([klass + cctor_finished/_or_no_cctor]) to "initialized". The
        // conditional class-init call then goes dead and is cleaned up, matching C# where the
        // static constructor runs implicitly.
        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                if (instruction.OpCode == OpCode.Move && i == 0 && instruction.Operands[0] is MemoryOperand)
                    continue;

                if (instruction.Operands[i] is MemoryOperand { Index: null, Scale: 0, Addend: 0xD8 or 0xE0, Base: LocalVariable { Type: RuntimeClassTypeAnalysisContext } })
                    instruction.SetOperand(i, new Immediate(1));
            }
        }

        // Fold bit tests on klass->bitflags1/2 where the tested bit is a compile-time property of
        // the type: valuetype (0x132&1), enumtype (0x132&4), nullabletype (0x132&8), is_interface
        // (0x133&0x10). Other bits (initialized, cctor flags) are runtime state and left alone.
        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (instruction.OpCode != OpCode.And || instruction.Operands.Count < 3)
                continue;

            for (var side = 1; side <= 2; side++)
            {
                if (instruction.Operands[side] is not Immediate { Value: var mask })
                    continue;

                var bitflagsMemory = instruction.Operands[side == 1 ? 2 : 1] switch
                {
                    MemoryOperand inline => inline,
                    LocalVariable local when ChaseCopies(definitions, local) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand loaded] } => loaded,
                    _ => (MemoryOperand?)null,
                };

                if (FoldBitTest(bitflagsMemory, mask) is not { } folded)
                    continue;

                instruction.OpCode = OpCode.Move;
                instruction.SetOperands(instruction.Operands[0], new Immediate(folded));
                break;
            }
        }

        foreach (var block in method.ControlFlowGraph.Blocks)
        {
            for (var i = 0; i < block.Instructions.Count; i++)
            {
                var instruction = block.Instructions[i];

                if (instruction.OpCode is not (OpCode.CheckEqual or OpCode.CheckNotEqual) || instruction.Operands.Count < 3)
                    continue;

                if (TryMatch(instruction, definitions) is not { } match)
                    continue;

                var isinstLocal = new LocalVariable("isinstResult", new Register(null, "rax"));
                method.Locals.Add(isinstLocal);
                block.Instructions.Insert(i, new Instruction(instruction.Index, OpCode.IsInst, isinstLocal, match.Object, match.Type));
                i++; // skip over the inserted instruction

                // entry == klass(T)  <=>  isinst(obj, T) != null
                instruction.SetOperand(1, isinstLocal);
                instruction.SetOperand(2, new Immediate(0));
                instruction.OpCode = instruction.OpCode == OpCode.CheckEqual ? OpCode.CheckNotEqual : OpCode.CheckEqual;
            }
        }
    }

    private static long? FoldBitTest(MemoryOperand? memory, long mask)
    {
        if (memory is not { Index: null, Scale: 0, Base: LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: { } type } } })
            return null;

        long? bit = (memory.Value.Addend, mask) switch
        {
            (0x132, 1) => type.IsValueType ? 1 : 0,
            (0x132, 4) => type.IsEnumType ? 1 : 0,
            (0x132, 8) => IsNullable(type) ? 1 : 0,
            (0x133, 0x10) => type.IsInterface ? 1 : 0,
            _ => null,
        };

        return bit == 1 ? mask : bit == 0 ? 0 : null;
    }

    private static bool IsNullable(TypeAnalysisContext type) =>
        type is GenericInstanceTypeAnalysisContext { GenericType.FullName: "System.Nullable`1" }
        || type.Definition is { Name: "Nullable`1" };

    private static (LocalVariable Object, TypeAnalysisContext Type)? TryMatch(Instruction check, Dictionary<LocalVariable, Instruction> definitions)
    {
        for (var side = 1; side <= 2; side++)
        {
            var type = ResolveTypeOperand(check.Operands[side], definitions);
            var entryOperand = check.Operands[side == 1 ? 2 : 1];

            if (type == null || type.IsValueType)
                continue;

            // entry = [th + idx*8 - 8]  (th[targetDepth - 1]), either inline in the comparison
            // (cmp [mem], reg) or loaded into a local first
            var entryMemory = entryOperand switch
            {
                MemoryOperand inline => inline,
                LocalVariable entryLocal when ChaseCopies(definitions, entryLocal) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand loaded] } => loaded,
                _ => (MemoryOperand?)null,
            };

            if (entryMemory is not { Scale: 8, Base: LocalVariable thLocal, Index: not null } mem
                || mem.Addend is not (0 or -8 or 0xFFFFFFF8L)) // th[depth-1]; 32-bit displacement may be kept unsigned
                continue;

            // th = [srcKlass + typeHierarchy] for class checks, or [srcKlass + interfaceOffsets]
            // for interface checks; both mean "obj's type hierarchy contains T"
            if (ChaseCopies(definitions, thLocal) is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Base: LocalVariable srcKlass } thMem] }
                || thMem.Addend is not (TypeHierarchyOffset64 or InterfaceOffsetsOffset64))
                continue;

            // srcKlass = [obj]  (obj->klass)
            if (ChaseCopies(definitions, srcKlass) is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable objLocal }] })
                continue;

            return (objLocal, type);
        }

        return null;
    }

    private static TypeAnalysisContext? ResolveTypeOperand(IOperand operand, Dictionary<LocalVariable, Instruction> definitions) =>
        operand switch
        {
            TypeAnalysisContext type => type,
            LocalVariable local when ChaseCopies(definitions, local) is { OpCode: OpCode.Move, Operands: [_, TypeAnalysisContext type] } => type,
            _ => null,
        };

    private static Instruction? ChaseCopies(Dictionary<LocalVariable, Instruction> definitions, LocalVariable local)
    {
        var visited = new HashSet<LocalVariable>();

        while (visited.Add(local))
        {
            if (!definitions.TryGetValue(local, out var definition))
                return null;

            if (definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable source] })
            {
                local = source;
                continue;
            }

            return definition;
        }

        return null;
    }
}
