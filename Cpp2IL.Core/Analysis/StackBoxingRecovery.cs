using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Native Enum.ToString can receive a stack object: class, monitor sentinel, payload.
// Recover the payload use before SSA/liveness discards its otherwise unread stores.
internal static class StackBoxingRecovery
{
    private record Store(Block Block, int Index, Instruction Instruction);

    internal static void Run(MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        foreach (var block in method.ControlFlowGraph!.Blocks)
            for (var index = 0; index < block.Instructions.Count; index++)
            {
                var call = block.Instructions[index];
                if (!call.IsCall || call.Operands.Count < 2)
                    continue;
                var target = call.Operands[0] as MethodAnalysisContext;
                if (call.Operands[0] is Immediate address
                    && method.AppContext.MethodsByAddress.TryGetValue(address.UnsignedValue, out var candidates)
                    && candidates is [{ } unique]) target = unique;
                // This BCL operation only observes the enum value, so replacing its borrowed
                // stack receiver with a managed box cannot expose a new object identity.
                if (target is not { IsStatic: false, Name: "ToString" }
                    || target.DeclaringType != method.AppContext.SystemTypes.EnumType
                    || target.ReturnType != method.AppContext.SystemTypes.SystemStringType)
                    continue;
                var receiverIndex = call.OpCode == OpCode.Call ? 2 : 1;
                if (call.Operands.Count <= receiverIndex
                    || Resolve(method, call.Operands[receiverIndex], block, index) is not AddressOf { Target: StackOffset header }
                    || (long)header.Offset + 2 * pointerSize + 8 > int.MaxValue
                    || Values(method, block, index, header.Offset, pointerSize) is not { } types
                    || types[0] is not TypeAnalysisContext { IsEnumType: true } type
                    || types.Any(t => !Equals(t, type))
                    || Values(method, block, index, header.Offset + pointerSize, pointerSize) is not { } monitors
                    || monitors.Any(m => m is not Immediate { Value: -1 }))
                    continue;
                var size = TypeSizes.UnboxedSize(type, pointerSize);
                var payload = new StackOffset(header.Offset + 2 * pointerSize, (int)size);
                if (size is not (1 or 2 or 4 or 8)
                    || Stores(block, index, payload.Offset, payload.AccessSize) == null)
                    continue;
                var boxed = new Register(null, $"boxed_stack_{header.Offset}_{call.Index}");
                block.Instructions.Insert(index++, new Instruction(-1, OpCode.Box, boxed, type, new AddressOf(payload)));
                call.SetOperand(receiverIndex, boxed);
            }
    }

    private static List<IOperand>? Values(MethodAnalysisContext method, Block block, int end, int offset, int size)
    {
        if (Stores(block, end, offset, size) is not { } stores)
            return null;
        var values = stores.Select(s => Resolve(method, s.Instruction.Operands[1], s.Block, s.Index)).ToList();
        return values.Any(v => v == null) ? null : values.Select(v => v!).ToList();
    }

    // Every incoming path must initialize the entire slot. Calls and unknown writes
    // invalidate the proof; partial/overlapping stores cannot establish a scalar value.
    private static List<Store>? Stores(Block block, int end, int offset, int size)
    {
        var budget = 512;
        return FindStores(block, end, offset, size, [], ref budget);
    }

    private static List<Store>? FindStores(Block block, int end, int offset, int size, HashSet<Block> path, ref int budget)
    {
        if (--budget < 0 || path.Count >= 64 || !path.Add(block)) return null;
        try
        {
            for (var i = end - 1; i >= 0; i--)
            {
                var instruction = block.Instructions[i];
                if (instruction.OpCode is OpCode.Call or OpCode.CallVoid or OpCode.IndirectCall || instruction.Destination is MemoryOperand)
                    return null;
                if (instruction.Destination is not StackOffset slot)
                    continue;
                if (slot.Offset >= (long)offset + size || (long)slot.Offset + Math.Max(slot.AccessSize, 1) <= offset)
                    continue;
                return instruction.OpCode == OpCode.Move && instruction.Operands.Count == 2
                    && slot.Offset == offset && slot.AccessSize == size
                    ? [new Store(block, i, instruction)] : null;
            }
            if (block.Predecessors.Count == 0) return null;
            var stores = new List<Store>();
            foreach (var predecessor in block.Predecessors)
            {
                var incoming = FindStores(predecessor, predecessor.Instructions.Count, offset, size, path, ref budget);
                if (incoming == null) return null;
                stores.AddRange(incoming);
            }
            return stores;
        }
        finally { path.Remove(block); }
    }

    private static IOperand? Resolve(MethodAnalysisContext method, IOperand operand, Block block, int end)
    {
        var budget = 512;
        return ResolveValue(method, operand, block, end, 0, ref budget);
    }

    private static IOperand? ResolveValue(MethodAnalysisContext method, IOperand operand, Block block, int end, int depth, ref int budget)
    {
        if (--budget < 0 || depth >= 64) return null;
        if (operand is TypeAnalysisContext or Immediate or AddressOf { Target: StackOffset }) return operand;
        if (operand is MemoryOperand { Index: null, Scale: 0 } memory)
        {
            if (memory.Base == null)
                return MetadataType(memory.Addend);
            var pointer = ResolveValue(method, memory.Base, block, end, depth + 1, ref budget);
            if (pointer is Immediate address) return MetadataType(unchecked(address.Value + memory.Addend));
            return null;
        }
        if (operand is not Register register) return null;
        for (var i = end - 1; i >= 0; i--)
        {
            var instruction = block.Instructions[i];
            if (instruction.OpCode is OpCode.Call or OpCode.CallVoid or OpCode.IndirectCall) return null;
            if (instruction.Destination is Register destination && destination.Number == register.Number)
                return instruction.OpCode == OpCode.Move && instruction.Operands.Count == 2
                    ? ResolveValue(method, instruction.Operands[1], block, i, depth + 1, ref budget) : null;
        }
        IOperand? value = null;
        foreach (var predecessor in block.Predecessors)
        {
            var incoming = ResolveValue(method, operand, predecessor, predecessor.Instructions.Count, depth + 1, ref budget);
            if (incoming == null || value != null && !Equals(incoming, value)) return null;
            value = incoming;
        }
        return value;

        IOperand? MetadataType(long address)
        {
            var context = method.AppContext.LibCpp2IlContext;
            if (address <= 0 || context.GetTypeGlobalByAddress((ulong)address) is not { } type) return null;
            var resolved = method.AppContext.ResolveIl2CppType(type);
            // ELF GOT entries can point to a metadata slot. Preserve that indirection;
            // once the class itself is loaded, another dereference is not the same class.
            var pointer = context.Binary.ReadPointerAtVirtualAddress((ulong)address);
            if (context.Binary.TryMapVirtualAddressToRaw(pointer, out _)
                && context.GetTypeGlobalByAddress(pointer) is { } indirect
                && method.AppContext.ResolveIl2CppType(indirect) == resolved)
                return new Immediate(unchecked((long)pointer));
            return resolved;
        }
    }
}
