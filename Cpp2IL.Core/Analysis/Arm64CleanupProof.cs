using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using Disarm.InternalDisassembly;
using LibCpp2IL.Elf;

namespace Cpp2IL.Core.Analysis;

// Deliberately not a general emulator: any unknown instruction, branch, call or
// memory effect rejects recovery. Only verified interface lookups are summarized.
internal sealed class Arm64CleanupProof
{
    private readonly ElfFile _binary;
    private readonly ElfExceptionTable _table;
    private readonly List<NativeDisposal> _disposals;
    private readonly Dictionary<ulong, Arm64Instruction> _code;
    private readonly HashSet<ulong> _raise;
    private readonly Dictionary<ulong, string?> _imports = [];
    private readonly record struct Value(int Kind, long Number); // constant, resource, exception, wrapper, catch slot

    internal Arm64CleanupProof(MethodAnalysisContext method, ElfExceptionTable table)
    {
        _binary = (ElfFile)method.AppContext.Binary;
        _table = table;
        _disposals = method.NativeDisposals;
        _code = Disassembler.Disassemble(method.RawBytes.AsSpan(), method.UnderlyingPointer,
            new Disassembler.Options(true, true, false)).ToList().ToDictionary(i => i.Address);
        var keys = method.AppContext.GetOrCreateKeyFunctionAddresses();
        _raise = [keys.il2cpp_raise_exception, keys.il2cpp_vm_exception_raise, keys.il2cpp_codegen_raise_exception];
        _raise.Remove(0);
    }

    internal bool Proves(ulong call, IReadOnlyList<NativeDisposal> expected)
    {
        var regs = new Dictionary<string, Value>();
        var stack = new Dictionary<long, Value>();
        for (var i = 0; i < expected.Count; i++)
            if (!regs.TryAdd(expected[i].Receiver, new Value(1, i))) return false;
        var seen = 0;
        var catching = false;
        bool? equal = null;
        var pc = call;
        if (!EnterCatch()) return expected.Count == 0 && _table.At(call)?.Landing is null or 0;
        for (var step = 0; step < 512; step++)
        {
            var disposal = _disposals.Find(d => d.Lookup == pc);
            if (disposal != null)
            {
                if (seen >= expected.Count || !ReferenceEquals(disposal, expected[seen])
                    || !regs.TryGetValue(disposal.Receiver, out var receiver) || receiver != new Value(1, seen)) return false;
                seen++;
                pc = disposal.Call.NativeAddress + 4;
                Clobber();
                continue;
            }
            if (!_code.TryGetValue(pc, out var insn)) return false;
            var next = pc + 4;
            switch (insn.Mnemonic)
            {
                case Arm64Mnemonic.NOP: break;
                case Arm64Mnemonic.MOV:
                    var moved = insn.Op1Kind == Arm64OperandKind.Immediate ? new Value(0, insn.Op1Imm) : Read(insn.Op1Reg);
                    if (moved == null || (insn.Op0Reg is >= Arm64Register.W0 and <= Arm64Register.W31 && moved.Value.Kind != 0)) return false;
                    regs[Name(insn.Op0Reg)] = moved.Value;
                    break;
                case Arm64Mnemonic.CMP:
                    var left = Read(insn.Op0Reg);
                    var right = insn.Op1Kind == Arm64OperandKind.Immediate ? new Value(0, insn.Op1Imm) : Read(insn.Op1Reg);
                    if (left == null || right == null) return false;
                    equal = left == right;
                    break;
                case Arm64Mnemonic.B:
                    if (insn.MnemonicConditionCode is Arm64ConditionCode.NONE or Arm64ConditionCode.AL) next = insn.BranchTarget;
                    else if (equal != null && insn.MnemonicConditionCode is Arm64ConditionCode.EQ or Arm64ConditionCode.NE)
                    { if (equal == (insn.MnemonicConditionCode == Arm64ConditionCode.EQ)) next = insn.BranchTarget; }
                    else return false;
                    break;
                case Arm64Mnemonic.CBZ:
                case Arm64Mnemonic.CBNZ:
                    if (Read(insn.Op0Reg) is not { } tested) return false;
                    if ((tested == new Value(0, 0)) == (insn.Mnemonic == Arm64Mnemonic.CBZ)) next = insn.BranchTarget;
                    break;
                case Arm64Mnemonic.TBZ:
                case Arm64Mnemonic.TBNZ:
                    if (Read(insn.Op0Reg) is not { Kind: 0 } bits) return false;
                    if (((bits.Number & (1L << (int)insn.Op1Imm)) == 0) == (insn.Mnemonic == Arm64Mnemonic.TBZ)) next = insn.BranchTarget;
                    break;
                case Arm64Mnemonic.LDR:
                case Arm64Mnemonic.LDUR:
                    if (insn.Op0Reg is not (>= Arm64Register.X0 and <= Arm64Register.X30)
                        || insn.MemIndexMode != Arm64MemoryIndexMode.Offset || insn.MemAddendReg != Arm64Register.INVALID) return false;
                    Value loaded;
                    if (IsStack(insn.MemBase))
                    { if (!stack.TryGetValue(insn.MemOffset, out loaded)) return false; }
                    else if (insn.MemOffset == 0 && Read(insn.MemBase) is { Kind: 4 }) loaded = new Value(2, 0);
                    else return false;
                    regs[Name(insn.Op0Reg)] = loaded;
                    break;
                case Arm64Mnemonic.STR:
                case Arm64Mnemonic.STUR:
                    if (!IsStack(insn.MemBase) || insn.Op0Reg is not (>= Arm64Register.X0 and <= Arm64Register.X30)
                        || insn.MemIndexMode != Arm64MemoryIndexMode.Offset || insn.MemAddendReg != Arm64Register.INVALID
                        || Read(insn.Op0Reg) is not { } stored) return false;
                    stack[insn.MemOffset] = stored;
                    break;
                case Arm64Mnemonic.BL:
                    if (_raise.Contains(insn.BranchTarget))
                    {
                        if (catching || Read(Arm64Register.X0) != new Value(2, 0)) return false;
                        if (_table.At(pc)?.Landing is null or 0) return seen == expected.Count;
                        if (!EnterCatch()) return false;
                        continue;
                    }
                    var import = Import(insn.BranchTarget);
                    if (import == "__cxa_begin_catch" && !catching && Read(Arm64Register.X0) == new Value(3, 0))
                    { Clobber(); catching = true; regs["X0"] = new Value(4, 0); }
                    else if (import == "__cxa_end_catch" && catching) { catching = false; Clobber(); }
                    else return false;
                    break;
                default: return false;
            }
            pc = next;
        }
        return false;

        Value? Read(Arm64Register register) => IsStack(register) ? new Value(0, 0) : regs.TryGetValue(Name(register), out var value) ? value : null;
        void Clobber() { for (var i = 0; i <= 18; i++) regs.Remove("X" + i); equal = null; }
        bool EnterCatch()
        {
            if (_table.At(pc) is not { Landing: not 0, Selector: > 0 } site) return false;
            Clobber(); regs["X0"] = new Value(3, 0); regs["X1"] = new Value(0, site.Selector); pc = site.Landing;
            return true;
        }
    }

    // Injected null/bounds throws are often outlined outside the hot native range.
    internal IEnumerable<(ulong Branch, ulong Throw)> OutlinedThrows(HashSet<ulong> throws)
    {
        foreach (var insn in _code.Values)
        {
            if (insn.Mnemonic is not (Arm64Mnemonic.CBZ or Arm64Mnemonic.CBNZ or Arm64Mnemonic.TBZ or Arm64Mnemonic.TBNZ or Arm64Mnemonic.B)) continue;
            var pc = insn.BranchTarget;
            for (var i = 0; i < 4 && _code.TryGetValue(pc, out var target); i++)
            {
                if (throws.Contains(pc)) { yield return (insn.Address, pc); break; }
                if (target.Mnemonic != Arm64Mnemonic.B || target.MnemonicConditionCode is not (Arm64ConditionCode.NONE or Arm64ConditionCode.AL)) break;
                pc = target.BranchTarget;
            }
        }
    }

    private string? Import(ulong address)
    {
        if (_imports.TryGetValue(address, out var name)) return name;
        name = null;
        if (_binary.TryMapVirtualAddressToRaw(address, out var raw) && raw >= 0 && raw <= _binary.RawLength - 16)
        {
            var thunk = Disassembler.Disassemble(_binary.GetRawBinaryContent().Slice((int)raw, 16), address,
                new Disassembler.Options(true, true, false)).ToList();
            if (thunk is [{ Mnemonic: Arm64Mnemonic.ADRP } page, { Mnemonic: Arm64Mnemonic.LDR } load,
                { Mnemonic: Arm64Mnemonic.ADD }, { Mnemonic: Arm64Mnemonic.BR } branch]
                && load.MemBase == page.Op0Reg && branch.Op0Reg == load.Op0Reg)
                name = _binary.GetImportNameAtSlot(unchecked((ulong)(((long)address & ~0xfffL) + page.Op1Imm + load.MemOffset)));
        }
        _imports[address] = name;
        return name;
    }
    private static bool IsStack(Arm64Register reg) => reg is Arm64Register.X31 or Arm64Register.W31;
    private static string Name(Arm64Register reg) => reg is >= Arm64Register.W0 and <= Arm64Register.W31
        ? "X" + (reg - Arm64Register.W0) : reg.ToString();
}
