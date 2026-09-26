using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Fully shared generic code keeps a value of type argument T in a stack buffer sized by T's class, as its
/// size is only known at run time: a runtime helper unboxes an object into such a buffer, buffers are copied
/// with memcpy (cleared with memset), and a second helper makes a constrained call on the value in one.
/// Model each buffer as a local of type T, so that reads <c>((T)obj).ToString()</c> again:
/// <list type="bullet">
/// <item>unbox helper (obj, T's class, buffer) => <c>t = (T)obj</c> (unbox.any T)</item>
/// <item>memcpy(buffer, buffer', size) => <c>t = t'</c>; a memset overwritten by one is dropped, a lone one is <c>default(T)</c></item>
/// <item>constrained-call helper (T's class, method, scratch, buffer, no arguments, result buffer) =>
/// <c>result = t.Method()</c>, the result going to the frame slot the result buffer points at</item>
/// </list>
/// A method is changed only when every buffer use fits these.
/// </summary>
public static class SharedValueStorageRecovery
{
    internal enum HelperKind
    {
        None,
        UnboxInto,
        ConstrainedInvoke,
    }

    private static readonly ConcurrentDictionary<(ApplicationAnalysisContext App, ulong Target), HelperKind> Helpers = new();

    // Il2CppClass::byval_arg's bit field word, whose top bit is valuetype, in the 64-bit v29-v31 layout.
    private const int ValueTypeWordOffset = 0x28;

    public static bool Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet
            || method.AppContext.Binary.PointerSizeBytes != 8 || method.AppContext.MetadataVersion is < 29 or >= 32
            || method.ControlFlowGraph is not { } graph)
            return false;

        var instructions = graph.Instructions;
        var buffers = instructions.Where(i => i is { OpCode: OpCode.LocalAllocate, Destination: LocalVariable })
            .Select(i => (LocalVariable)i.Destination!).ToHashSet();
        if (buffers.Count == 0)
            return false;

        var definitions = instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());

        TypeAnalysisContext? typeArgument = null;
        bool IsTypeArgumentClass(IOperand operand)
        {
            // The class is the RGCTX constant itself, or a local holding it.
            var klass = operand is LocalVariable { Type: RuntimeClassTypeAnalysisContext typed } ? typed : operand as RuntimeClassTypeAnalysisContext;
            if (klass is not { RepresentedType: GenericParameterTypeAnalysisContext type })
                return false;
            if (typeArgument != null && typeArgument != type)
                return false;
            typeArgument = type;
            return true;
        }

        var unboxes = new List<Instruction>();
        var invokes = new List<Instruction>();
        var copies = new List<Instruction>();
        var clears = new List<Instruction>();
        foreach (var instruction in instructions)
        {
            switch (instruction)
            {
                case { OpCode: OpCode.Call, Operands: [Immediate target, LocalVariable, _, var klass, LocalVariable buffer, ..] }
                    when buffers.Contains(buffer) && IsTypeArgumentClass(klass) && Kind(method.AppContext, target.UnsignedValue) == HelperKind.UnboxInto:
                    unboxes.Add(instruction);
                    break;
                case { OpCode: OpCode.Call, Operands: [Immediate target, _, var klass, var calledInfo, LocalVariable scratch,
                        LocalVariable storage, Immediate { Value: 0 }, LocalVariable, ..] }
                    when buffers.Contains(scratch) && buffers.Contains(storage) && IsTypeArgumentClass(klass) && CalledMethod(calledInfo) != null
                         && Kind(method.AppContext, target.UnsignedValue) == HelperKind.ConstrainedInvoke:
                    invokes.Add(instruction);
                    break;
                case { OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: "MemCpy", DeclaringType.Name: "UnsafeUtility" }, LocalVariable destination, ..] }
                    when buffers.Contains(destination):
                    copies.Add(instruction);
                    break;
                case { OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: "MemSet", DeclaringType.Name: "UnsafeUtility" }, LocalVariable destination, Immediate { Value: 0 }, ..] }
                    when buffers.Contains(destination):
                    clears.Add(instruction);
                    break;
            }
        }

        if (typeArgument == null || unboxes.Count == 0 && invokes.Count == 0)
            return false;

        // Each buffer gets its value from exactly one place: an unbox, or a copy (a clear before it is dead).
        var valueOf = new Dictionary<LocalVariable, LocalVariable>();
        var returnedBuffer = new Dictionary<LocalVariable, LocalVariable>();
        LocalVariable NewValue()
        {
            var value = new LocalVariable($"sharedValue{method.Locals.Count}", new Register(null, $"shared_value_{method.Locals.Count}"), typeArgument);
            method.Locals.Add(value);
            return value;
        }

        LocalVariable? Buffer(IOperand operand) => operand is LocalVariable local
            ? buffers.Contains(local) ? local : returnedBuffer.GetValueOrDefault(local)
            : null;

        var defined = new HashSet<LocalVariable>();
        foreach (var unbox in unboxes)
        {
            var buffer = (LocalVariable)unbox.Operands[4];
            if (!defined.Add(buffer))
                return false;
            returnedBuffer[(LocalVariable)unbox.Operands[1]] = buffer; // the helper hands the buffer back
        }
        foreach (var copy in copies)
            if (copy.Operands.Count < 3 || Buffer(copy.Operands[2]) == null || !defined.Add((LocalVariable)copy.Operands[1]))
                return false;
        foreach (var invoke in invokes)
            if (!defined.Contains((LocalVariable)invoke.Operands[5]) && !clears.Any(c => c.Operands[1] == invoke.Operands[5]))
                return false;

        // Resolve everything before rewriting anything, so a method that does not fit is left untouched.
        var results = new Dictionary<Instruction, LocalVariable>();
        foreach (var invoke in invokes)
        {
            var called = CalledMethod(invoke.Operands[3])!;
            if (called.IsStatic || called.Parameters.Count != 0 || called.IsVoid || called.ReturnType is GenericParameterTypeAnalysisContext
                || ResultSlot(method, (LocalVariable)invoke.Operands[7], definitions) is not { } slot)
                return false;
            results[invoke] = slot;
        }

        foreach (var unbox in unboxes)
        {
            var value = NewValue();
            valueOf[(LocalVariable)unbox.Operands[4]] = value;
            var boxed = unbox.Operands[2];
            unbox.OpCode = OpCode.Unbox;
            unbox.SetOperands(value, typeArgument, boxed);
        }

        foreach (var copy in copies)
        {
            var source = valueOf.GetValueOrDefault(Buffer(copy.Operands[2])!);
            if (source == null)
                continue; // a copy from a buffer given its value only later is left as it is
            var value = NewValue();
            valueOf[(LocalVariable)copy.Operands[1]] = value;
            copy.OpCode = OpCode.Move;
            copy.SetOperands(value, source);
        }

        foreach (var clear in clears)
        {
            var buffer = (LocalVariable)clear.Operands[1];
            if (valueOf.ContainsKey(buffer))
            {
                clear.OpCode = OpCode.Nop;
                clear.SetOperands();
                continue;
            }
            var value = NewValue();
            valueOf[buffer] = value;
            clear.OpCode = OpCode.Move;
            clear.SetOperands(value, new Immediate(0));
        }

        foreach (var invoke in invokes)
        {
            if (!valueOf.TryGetValue((LocalVariable)invoke.Operands[5], out var receiver))
                continue;
            var called = CalledMethod(invoke.Operands[3])!;
            invoke.SetOperands(called, results[invoke], receiver);
        }
        // A buffer none of whose uses is left needs no stack space: drop the allocation, and with it
        // the size computation that only it read.
        var used = graph.Instructions.SelectMany(DeadCodeEliminator.UsedLocals).ToHashSet();
        foreach (var allocation in graph.Instructions.Where(i => i is { OpCode: OpCode.LocalAllocate, Destination: LocalVariable buffer } && !used.Contains(buffer)))
        {
            allocation.OpCode = OpCode.Nop;
            allocation.SetOperands();
        }
        DeadCodeEliminator.Run(graph);

        return true;
    }

    // The method a MethodInfo operand denotes: the constant itself, or a local holding it.
    private static MethodAnalysisContext? CalledMethod(IOperand operand) => operand switch
    {
        RuntimeMethodInfoAnalysisContext info => info.RepresentedMethod,
        LocalVariable { Type: RuntimeMethodInfoAnalysisContext typed } => typed.RepresentedMethod,
        _ => null
    };

    // The frame slot a result buffer address points at: its stack offset read from the slot naming,
    // e.g. &stack_-50 - 16 is stack_-60, whose reads the callee's write defines.
    private static LocalVariable? ResultSlot(MethodAnalysisContext method, LocalVariable pointer, Dictionary<LocalVariable, Instruction> definitions)
    {
        if (!definitions.TryGetValue(pointer, out var definition)
            || definition is not { OpCode: OpCode.Add or OpCode.Subtract, Operands: [_, AddressOf { Target: LocalVariable frame }, Immediate delta] }
            || StackOffset(frame.Register.Name) is not { } offset)
            return null;
        var target = definition.OpCode == OpCode.Add ? offset + delta.Value : offset - delta.Value;
        var name = target < 0 ? $"stack_-{-target:X}" : $"stack_{target:X}";
        var read = method.ControlFlowGraph!.Instructions.SelectMany(i => i.Sources).OfType<LocalVariable>()
            .Where(l => l.Register.Name == name && !definitions.ContainsKey(l)).Distinct().ToList();
        return read is [{ } slot] ? slot : null;
    }

    private static long? StackOffset(string? name)
    {
        if (name == null || !name.StartsWith("stack_", StringComparison.Ordinal))
            return null;
        var text = name["stack_".Length..];
        var negative = text.StartsWith('-');
        return long.TryParse(negative ? text[1..] : text, NumberStyles.HexNumber, CultureInfo.InvariantCulture, out var value)
            ? negative ? -value : value
            : null;
    }

    private static HelperKind Kind(ApplicationAnalysisContext app, ulong target) => Helpers.GetOrAdd((app, target), key =>
    {
        var binary = key.App.Binary;
        if (key.Target >= key.App.ManagedCodeStart && key.Target <= key.App.ManagedCodeEnd
            || key.App.MethodsByAddress.ContainsKey(key.Target)
            || !binary.TryMapVirtualAddressToRaw(key.Target, out var raw) || raw < 0 || raw > binary.RawLength - 40)
            return HelperKind.None;
        return Classify(binary.GetRawBinaryContent().Slice((int)raw, 40), key.Target);
    });

    /// <summary>
    /// Both helpers first test whether T is a value type: a load of its class's byval_arg bit word followed by a
    /// TBNZ on that register. The class comes in X1 for the unbox helper (obj, class, buffer) and in X0 for the
    /// constrained-call helper (class, method, ...).
    /// </summary>
    internal static HelperKind Classify(ReadOnlySpan<byte> bytes, ulong address)
    {
        List<Arm64Instruction> code;
        try
        {
            code = Disassembler.Disassemble(bytes, address, new Disassembler.Options(true, true, false)).ToList();
        }
        catch
        {
            return HelperKind.None;
        }

        var load = code.FindIndex(i => i is { Mnemonic: Arm64Mnemonic.LDR, MemOffset: ValueTypeWordOffset }
            && i.MemBase is Arm64Register.X0 or Arm64Register.X1 && i.Op0Reg is >= Arm64Register.W0 and <= Arm64Register.W30);
        if (load < 0 || code.Take(load).Any(i => i.Mnemonic is not (Arm64Mnemonic.STP or Arm64Mnemonic.STR or Arm64Mnemonic.SUB))
            || !code.Skip(load + 1).Any(i => i.Mnemonic == Arm64Mnemonic.TBNZ && i.Op0Reg == code[load].Op0Reg))
            return HelperKind.None;
        return code[load].MemBase == Arm64Register.X1 ? HelperKind.UnboxInto : HelperKind.ConstrainedInvoke;
    }
}
