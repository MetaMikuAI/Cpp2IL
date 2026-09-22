using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Analysis;

// Native compilation can emit a second body without registering it in the method table.
// Recover only a unique, complete instruction match; never match names or game addresses.
internal static class NativeMethodCloneRecovery
{
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext, Cache> Caches = new();

    private sealed class Cache(ApplicationAnalysisContext app)
    {
        internal readonly ConcurrentDictionary<ulong, string> Bodies = new();
        internal readonly ConcurrentDictionary<TypeAnalysisContext, Dictionary<string, MethodAnalysisContext?>> Indices = new();

        internal string Body(ulong address) => Bodies.GetOrAdd(address, start =>
        {
            try
            {
                var raw = (int)app.Binary.MapVirtualAddressToRaw(start);
                if (raw <= 0) return "";
                var bytes = app.Binary.GetRawBinaryContent();
                var instructions = Disassembler.Disassemble(bytes.Slice(raw, Math.Min(512, bytes.Length - raw)), start,
                    new Disassembler.Options(true, true, false)).ToList();
                var keys = app.GetOrCreateKeyFunctionAddresses();
                return Fingerprint(instructions, target => target == keys.il2cpp_codegen_initialize_method
                    || target == keys.il2cpp_codegen_initialize_runtime_metadata, HiddenArgument) ?? "";
            }
            catch (Exception) { return ""; } // An undecodable or out-of-range body is not proof.
        });

        private Arm64Register? HiddenArgument(ulong target)
        {
            if (!app.MethodsByAddress.TryGetValue(target, out var methods) || methods is not [{ } method]
                || method.GenericParameters.Count != 0 || method.DeclaringType?.GenericParameters.Count != 0
                || method is ConcreteGenericMethodAnalysisContext) return null;
            var arguments = app.InstructionSet.CallingConventionResolver!.ResolveForManaged(method);
            return arguments.LastOrDefault() is Register register && Enum.TryParse<Arm64Register>(register.Name, out var native)
                ? native : null;
        }

        internal Dictionary<string, MethodAnalysisContext?> Index(TypeAnalysisContext returnType) => Indices.GetOrAdd(returnType, type =>
        {
            var index = new Dictionary<string, MethodAnalysisContext?>();
            foreach (var method in app.Assemblies.SelectMany(a => a.Types).Where(t => t.IsValueType && t.GenericParameters.Count == 0)
                .SelectMany(t => t.Methods).Where(m => !m.IsStatic && m.Parameters.Count == 0 && m.GenericParameters.Count == 0
                    && m.ReturnType == type && m.UnderlyingPointer != 0))
            {
                var body = Body(method.UnderlyingPointer);
                if (body.Length == 0) continue;
                // Even identical machine code does not identify a unique managed signature.
                if (index.ContainsKey(body)) index[body] = null;
                else index.Add(body, method);
            }
            return index;
        });
    }

    internal static bool Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet) return false;
        var changed = false;
        foreach (var call in method.ControlFlowGraph!.Instructions)
        {
            if (call is not { OpCode: OpCode.Call, Operands: [Immediate target, LocalVariable { Type: { IsValueType: true } type }, ..] }
                || method.AppContext.MethodsByAddress.ContainsKey(target.UnsignedValue)) continue;
            var cache = Caches.GetValue(method.AppContext, app => new Cache(app));
            var body = cache.Body(target.UnsignedValue);
            if (body.Length == 0 || !cache.Index(type).TryGetValue(body, out var resolved) || resolved == null) continue;
            call.SetOperand(0, resolved);
            method.AppContext.InstructionSet.CallingConventionResolver!.RemapRawArguments(call, resolved);
            changed = true;
        }
        return changed;
    }

    internal static string? Fingerprint(IReadOnlyList<Arm64Instruction> window, Func<ulong, bool> isInitializer,
        Func<ulong, Arm64Register?> hiddenArgument)
    {
        if (window.Count == 0) return null;
        var byAddress = window.ToDictionary(i => i.Address);
        var live = new SortedDictionary<ulong, Arm64Instruction>();
        var pending = new Queue<ulong>();
        pending.Enqueue(window[0].Address);
        while (pending.TryDequeue(out var address))
        {
            if (live.ContainsKey(address)) continue;
            if (!byAddress.TryGetValue(address, out var instruction) || instruction.Mnemonic == Arm64Mnemonic.INVALID) return null;
            live.Add(address, instruction);
            if (instruction.Mnemonic is Arm64Mnemonic.RET or Arm64Mnemonic.RETAA or Arm64Mnemonic.RETAB) continue;
            if (instruction.Mnemonic == Arm64Mnemonic.BR) return null;
            if (IsBranch(instruction))
            {
                // An external tail branch or a body beyond the bounded window is not a match.
                pending.Enqueue(BranchTarget(instruction));
                if (instruction.Mnemonic == Arm64Mnemonic.B
                    && instruction.MnemonicConditionCode is Arm64ConditionCode.NONE or Arm64ConditionCode.AL) continue;
            }
            pending.Enqueue(address + 4);
        }
        var body = live.Values.ToList();
        if (body.Count < 8) return null;
        var skipped = new HashSet<ulong>();
        // Recognize only the standard boolean metadata initialization guard. Its data
        // references and initializer calls remain in the fingerprint; only the private
        // once flag and its conditional execution are normalized.
        for (var i = 0; i + 3 < body.Count; i++)
        {
            var page = body[i]; var load = body[i + 1];
            if (page.Mnemonic != Arm64Mnemonic.ADRP || load.Mnemonic != Arm64Mnemonic.LDRB || load.MemBase != page.Op0Reg) continue;
            var branchIndex = i + 2;
            if (body[branchIndex].Mnemonic == Arm64Mnemonic.MOV) branchIndex++;
            var branch = body[branchIndex];
            if (branch.Op0Reg != load.Op0Reg || !(branch.Mnemonic == Arm64Mnemonic.CBNZ
                || branch.Mnemonic == Arm64Mnemonic.TBNZ && branch.Op1Imm == 0)) continue;
            var end = body.FindIndex(x => x.Address == BranchTarget(branch));
            if (end < branchIndex + 6) continue;
            var one = body[end - 2]; var store = body[end - 1];
            if (one.Mnemonic != Arm64Mnemonic.MOV || one.Op0Reg != load.Op0Reg || one.Op1Kind != Arm64OperandKind.Immediate || one.Op1Imm != 1
                || store.Mnemonic != Arm64Mnemonic.STRB || store.Op0Reg != load.Op0Reg || store.MemBase != page.Op0Reg || store.MemOffset != load.MemOffset) continue;
            var initialization = body.Skip(branchIndex + 1).Take(end - branchIndex - 3).ToList();
            if (initialization.Count == 0 || initialization.Count % 3 != 0) continue;
            var valid = true;
            for (var j = 0; j < initialization.Count; j += 3)
                valid &= initialization[j].Mnemonic == Arm64Mnemonic.ADRP && initialization[j].Op0Reg == Arm64Register.X0
                    && initialization[j + 1].Mnemonic == Arm64Mnemonic.LDR && initialization[j + 1].Op0Reg == Arm64Register.X0
                    && initialization[j + 1].MemBase == Arm64Register.X0
                    && initialization[j + 2].Mnemonic == Arm64Mnemonic.BL && isInitializer(initialization[j + 2].BranchTarget);
            if (!valid) continue;
            foreach (var removed in new[] { page, load, branch, one, store }) skipped.Add(removed.Address);
        }
        for (var i = 0; i + 1 < body.Count; i++)
            if (body[i].Mnemonic == Arm64Mnemonic.MOV && body[i].Op1Kind == Arm64OperandKind.Register && body[i].Op1Reg == Arm64Register.X31
                && body[i + 1].Mnemonic == Arm64Mnemonic.BL && hiddenArgument(body[i + 1].BranchTarget) == body[i].Op0Reg)
                skipped.Add(body[i].Address);

        var labels = new Dictionary<ulong, int>();
        var index = 0;
        foreach (var instruction in body)
        {
            labels[instruction.Address] = index;
            if (!skipped.Contains(instruction.Address)) index++;
        }
        var result = new List<string>();
        foreach (var instruction in body.Where(i => !skipped.Contains(i.Address)))
        {
            var text = instruction.ToString();
            text = text[(text.IndexOf(' ') + 1)..];
            if (instruction.Mnemonic == Arm64Mnemonic.ADRP)
                text = $"ADRP {instruction.Op0Reg}, {unchecked((ulong)((long)(instruction.Address & ~4095UL) + instruction.Op1Imm)):X}";
            else if (instruction.Mnemonic == Arm64Mnemonic.ADR)
                text = $"ADR {instruction.Op0Reg}, {unchecked((ulong)((long)instruction.Address + instruction.Op1Imm)):X}";
            else if (IsBranch(instruction))
                text = text[..text.LastIndexOf("0x", StringComparison.Ordinal)] + "label" + labels[BranchTarget(instruction)];
            result.Add(text);
        }
        return string.Join("\n", result);
    }

    private static bool IsBranch(Arm64Instruction instruction) => instruction.Mnemonic is
        Arm64Mnemonic.B or Arm64Mnemonic.CBZ or Arm64Mnemonic.CBNZ or Arm64Mnemonic.TBZ or Arm64Mnemonic.TBNZ;

    private static ulong BranchTarget(Arm64Instruction instruction) => instruction.Mnemonic switch
    {
        Arm64Mnemonic.CBZ or Arm64Mnemonic.CBNZ => unchecked((ulong)((long)instruction.Address + instruction.Op1Imm)),
        Arm64Mnemonic.TBZ or Arm64Mnemonic.TBNZ => unchecked((ulong)((long)instruction.Address + instruction.Op2Imm)),
        _ => instruction.BranchTarget
    };
}
