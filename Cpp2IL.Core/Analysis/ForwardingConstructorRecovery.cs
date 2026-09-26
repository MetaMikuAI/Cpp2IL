using System;
using System.Buffers.Binary;
using System.Linq;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Native inlining can leave only the base constructor call at an allocation site.
// Restore the allocated type's constructor only when its entire body forwards that call.
internal static class ForwardingConstructorRecovery
{
    internal static MethodAnalysisContext? Resolve(TypeAnalysisContext allocated, MethodAnalysisContext called)
    {
        // ILSpy can hide a lifted closure together with an unrecovered nested async
        // state machine while leaving references to it. Keep that declaration visible.
        if (allocated.NestedTypes.Count != 0) return null;
        if (allocated.AppContext.InstructionSet is not NewArmV8InstructionSet
            || allocated.IsValueType || allocated is GenericInstanceTypeAnalysisContext
            || allocated.GenericParameters.Count != 0 || allocated.BaseType != called.DeclaringType
            || called is not { Name: ".ctor", IsStatic: false, Parameters.Count: 0, UnderlyingPointer: not 0 })
            return null;
        return ForwardingConstructor(allocated, called);
    }

    // Native inlining can also leave a constructor calling a further ancestor's constructor in place
    // of its base type's. Restore the base constructor only when its entire body forwards that call.
    internal static MethodAnalysisContext? ResolveBaseCall(TypeAnalysisContext caller, MethodAnalysisContext called)
    {
        if (caller.AppContext.InstructionSet is not NewArmV8InstructionSet
            || caller.BaseType is not { IsValueType: false } direct || direct is GenericInstanceTypeAnalysisContext
            || direct.GenericParameters.Count != 0 || direct == called.DeclaringType
            || called is not { Name: ".ctor", IsStatic: false, Parameters.Count: 0, UnderlyingPointer: not 0 })
            return null;
        for (var ancestor = direct.BaseType; ancestor != called.DeclaringType; ancestor = ancestor.BaseType)
            if (ancestor == null) return null;
        return ForwardingConstructor(direct, called);
    }

    // The type's only parameterless constructor, if its whole body is a tail call to the called one.
    private static MethodAnalysisContext? ForwardingConstructor(TypeAnalysisContext type, MethodAnalysisContext called)
    {
        var constructors = type.Methods.Where(m => m is
            { Name: ".ctor", IsStatic: false, Parameters.Count: 0, UnderlyingPointer: not 0 }).ToList();
        if (constructors is not [{ } constructor]) return null;
        var binary = type.AppContext.Binary;
        if (!binary.TryMapVirtualAddressToRaw(constructor.UnderlyingPointer, out var raw)) return null;
        var bytes = binary.GetRawBinaryContent();
        if (raw < 0 || raw > bytes.Length - 8
            || !binary.TryMapVirtualAddressToRaw(constructor.UnderlyingPointer + 7, out var last) || last != raw + 7) return null;
        return ForwardedTarget(bytes.Slice((int)raw, 8), constructor.UnderlyingPointer) == called.UnderlyingPointer
            ? constructor : null;
    }

    // A tail B ends the body. The only optional instruction clears the hidden
    // MethodInfo argument X1; X0 (this), memory and all managed arguments are untouched.
    internal static ulong? ForwardedTarget(ReadOnlySpan<byte> body, ulong address)
    {
        if (body.Length < 4) return null;
        var word = BinaryPrimitives.ReadUInt32LittleEndian(body);
        if (word == 0xAA1F03E1) // MOV X1, XZR
        {
            if (body.Length < 8) return null;
            word = BinaryPrimitives.ReadUInt32LittleEndian(body[4..]);
            address += 4;
        }
        if ((word & 0xFC000000) != 0x14000000) return null;
        return unchecked((ulong)((long)address + ((int)(word << 6) >> 4)));
    }
}
