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
    {
        if (binary is not ElfStyleRelocationsBinary elf || binary.is32Bit
            || !binary.TryMapVirtualAddressToRaw(address, out var raw)
            || raw < 0 || raw > binary.RawLength - 16)
            return null;
        return ImportSlot(binary.GetRawBinaryContent().Slice((int)raw, 16), address) is { } slot
            ? elf.GetImportNameAtSlot(slot) : null;
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

    internal static int? IntegerArgumentCount(string? name) => name switch
    {
        "memcpy" or "memmove" or "memset" or "memcmp" => 3,
        "__memcpy_chk" or "__memmove_chk" or "__memset_chk" => 4,
        _ => null
    };
}
