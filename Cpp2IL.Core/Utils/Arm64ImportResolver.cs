using System;
using System.Linq;
using Disarm;
using Disarm.InternalDisassembly;
using LibCpp2IL;
using LibCpp2IL.Elf;

namespace Cpp2IL.Core.Utils;

internal static class Arm64ImportResolver
{
    internal static string? Resolve(Il2CppBinary binary, ulong address)
        => binary is ElfStyleRelocationsBinary elf && ImportSlot(binary, address) is { } slot
            ? elf.GetImportNameAtSlot(slot) : null;

    // Whether address is a standard ELF PLT entry, named import or not.
    internal static bool IsImportStub(Il2CppBinary binary, ulong address) => ImportSlot(binary, address) != null;

    private static ulong? ImportSlot(Il2CppBinary binary, ulong address)
    {
        if (binary is not ElfStyleRelocationsBinary || binary.is32Bit
            || !binary.TryMapVirtualAddressToRaw(address, out var raw)
            || raw < 0 || raw > binary.RawLength - 16)
            return null;
        return ImportSlot(binary.GetRawBinaryContent().Slice((int)raw, 16), address);
    }

    // Match the standard ELF PLT entry using only ABI scratch registers. Argument-
    // adjusting wrappers and unrelated GOT loads are not evidence of this signature.
    internal static ulong? ImportSlot(ReadOnlySpan<byte> bytes, ulong address)
    {
        if (bytes.Length != 16) return null;
        var code = Disassembler.Disassemble(bytes, address, new Disassembler.Options(true, true, false)).ToList();
        if (code is not [
                { Mnemonic: Arm64Mnemonic.ADRP, Op0Reg: Arm64Register.X16 } page,
                { Mnemonic: Arm64Mnemonic.LDR, Op0Reg: Arm64Register.X17, MemBase: Arm64Register.X16,
                    MemIndexMode: Arm64MemoryIndexMode.Offset, MemAddendReg: Arm64Register.INVALID } load,
                { Mnemonic: Arm64Mnemonic.ADD, Op0Reg: Arm64Register.X16, Op1Reg: Arm64Register.X16,
                    Op2Kind: Arm64OperandKind.Immediate } add,
                { Mnemonic: Arm64Mnemonic.BR, Op0Reg: Arm64Register.X17 }]
            || add.Op2Imm != load.MemOffset)
            return null;
        return unchecked((ulong)(((long)address & ~0xfffL) + page.Op1Imm + load.MemOffset));
    }

    internal enum NativeMathKind
    {
        // A managed method declared as an intrinsic with this C function's definition.
        Method,
        // The IL rem instruction, which IL2CPP compiles to fmod/fmodf for floating-point operands.
        Remainder,
        // Math(F).ModF(x, &integral), whose integral part is written through X0.
        ModF,
    }

    internal readonly record struct NativeMathFunction(NativeMathKind Kind, string TypeName, string MethodName, bool IsDouble, int Arity);

    // C math functions that compute exactly what one managed operation does. Their arguments and
    // result are in S0.. (D0.. for double), so no integer register other than ModF's pointer takes part.
    internal static NativeMathFunction? MathFunction(string? name) => name switch
    {
        "fmodf" => new(NativeMathKind.Remainder, "", "", false, 2),
        "fmod" => new(NativeMathKind.Remainder, "", "", true, 2),
        "modff" => new(NativeMathKind.ModF, "System.MathF", "ModF", false, 1),
        "modf" => new(NativeMathKind.ModF, "System.Math", "ModF", true, 1),
        "atan2f" or "powf" => new(NativeMathKind.Method, "System.MathF", MathMethodName(name[..^1]), false, 2),
        "atan2" or "pow" => new(NativeMathKind.Method, "System.Math", MathMethodName(name), true, 2),
        "sinf" or "cosf" or "tanf" or "asinf" or "acosf" or "atanf" or "sinhf" or "coshf" or "tanhf"
            or "expf" or "logf" or "log10f" or "cbrtf"
            => new(NativeMathKind.Method, "System.MathF", MathMethodName(name[..^1]), false, 1),
        "sin" or "cos" or "tan" or "asin" or "acos" or "atan" or "sinh" or "cosh" or "tanh"
            or "exp" or "log" or "log10" or "cbrt"
            => new(NativeMathKind.Method, "System.Math", MathMethodName(name), true, 1),
        _ => null
    };

    private static string MathMethodName(string name) => char.ToUpperInvariant(name[0]) + name[1..];

    // C memory functions and the UnsafeUtility method taking the same arguments in the same order
    // (size_t size => long size, int c => byte value), so the call maps over without any reordering.
    internal static string? MemoryMethodName(string? name) => name switch
    {
        "memcpy" => "MemCpy",
        "memmove" => "MemMove",
        "memset" => "MemSet",
        "memcmp" => "MemCmp",
        _ => null
    };

    internal static int? IntegerArgumentCount(string? name) => name switch
    {
        "memcpy" or "memmove" or "memset" or "memcmp" => 3,
        "__memcpy_chk" or "__memmove_chk" or "__memset_chk" => 4,
        _ => null
    };
}
