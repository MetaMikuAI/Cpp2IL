using System;
using System.Buffers.Binary;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// IL2CPP compiles <c>Interlocked.CompareExchange&lt;T&gt;</c> for a reference T into a direct call to the
/// runtime's pointer compare-exchange, a native function with no managed method of its own. The
/// function is recognized by its body: an acquire/release exclusive loop that stores X1 into [X0] when
/// [X0] equals X2, the GC write barrier on X0 and X1, and the value loaded from [X0] as the result. T is the
/// type of the field whose address the caller passes, so a site binds only when that address is a
/// field of the method's own receiver. The shared instantiation, when the linker folded it into the
/// same body, is specialized the same way: its hidden method argument is never passed here.
/// </summary>
public static class InterlockedHelperRecovery
{
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext, ConcurrentDictionary<ulong, bool>> Helpers = new();
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext, StrongBox<MethodAnalysisContext?>> CompareExchangeMethods = new();

    private const int HelperLength = 17;

    public static void Run(MethodAnalysisContext method)
    {
        var app = method.AppContext;
        if (app.InstructionSet.CallingConventionResolver is not { } conventions || method.ControlFlowGraph is not { } graph)
            return;

        Dictionary<LocalVariable, Instruction?>? definitions = null;
        foreach (var call in graph.Instructions)
        {
            if (call.OpCode is not (OpCode.Call or OpCode.CallVoid) || call.Operands is not [Immediate target, ..]
                || !IsReferenceCompareExchange(app, target.UnsignedValue) || !conventions.HasRawArgumentLayout(call, app))
                continue;

            if (definitions == null)
            {
                definitions = new Dictionary<LocalVariable, Instruction?>();
                foreach (var instruction in graph.Instructions)
                    if (instruction.Destination is LocalVariable local)
                        definitions[local] = definitions.ContainsKey(local) ? null : instruction;
            }

            var location = call.Operands[call.OpCode == OpCode.CallVoid ? 1 : 2];
            if (ReceiverFieldType(location, definitions) is not { IsValueType: false } fieldType
                || CompareExchange(app) is not { } generic)
                continue;

            var resolved = generic.MakeGenericInstanceMethod(fieldType);
            call.SetOperand(0, resolved);
            conventions.RemapRawArguments(call, resolved);
        }
    }

    // The declared type of the receiver field an address operand points at, when that is provable.
    internal static TypeAnalysisContext? ReceiverFieldType(IOperand location, Dictionary<LocalVariable, Instruction?> definitions)
    {
        if (location is AddressOf { Target: FieldReference direct })
            return direct.IsNested ? null : direct.Field.FieldType;
        if (location is not LocalVariable address || !definitions.TryGetValue(address, out var definition) || definition == null)
            return null;
        // The address is often computed once before a retry loop and copied into X0 on each pass.
        var copies = new HashSet<LocalVariable> { address };
        while (definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable original] } && copies.Add(original)
               && definitions.TryGetValue(original, out var next) && next != null)
            definition = next;
        if (definition is { OpCode: OpCode.Move, Operands: [_, AddressOf { Target: FieldReference moved }] })
            return moved.IsNested ? null : moved.Field.FieldType;
        if (definition is not { OpCode: OpCode.Add, Operands: [_, var left, var right] })
            return null;
        if (left is Immediate) (left, right) = (right, left);
        var seen = new HashSet<LocalVariable>();
        while (left is LocalVariable { IsThis: false } copy && seen.Add(copy) && definitions.TryGetValue(copy, out var source)
               && source is { OpCode: OpCode.Move, Operands: [_, LocalVariable copied] })
            left = copied;
        // The implicit receiver is never reassigned, so its field layout holds wherever the address is used.
        if (left is not LocalVariable { IsThis: true, Type: { IsValueType: false } owner } receiver || definitions.ContainsKey(receiver)
            || right is not Immediate { Value: >= 0 and <= int.MaxValue } offset
            || owner is GenericInstanceTypeAnalysisContext || owner.GenericParameters.Count != 0)
            return null;
        return owner.Fields.Where(f => !f.IsStatic && f.Offset == offset.Value).ToList() is [{ } field] ? field.FieldType : null;
    }

    private static MethodAnalysisContext? CompareExchange(ApplicationAnalysisContext app)
        => CompareExchangeMethods.GetValue(app, a => new StrongBox<MethodAnalysisContext?>(
            a.GetAssemblyByName("mscorlib")?.GetTypeByFullName("System.Threading.Interlocked")?.Methods
                .SingleOrDefault(m => m is { IsStatic: true, Name: "CompareExchange" } && m.GenericParameters.Count == 1
                    && m.Parameters.Count == 3 && m.Parameters[0].ParameterType is ByRefTypeAnalysisContext))).Value;

    internal static bool IsReferenceCompareExchange(ApplicationAnalysisContext app, ulong address)
        => Helpers.GetValue(app, _ => new ConcurrentDictionary<ulong, bool>()).GetOrAdd(address, start =>
        {
            // Identical code folding can give the shared instantiation of CompareExchange<T> this body.
            if (app.InstructionSet is not NewArmV8InstructionSet)
                return false;
            if (app.MethodsByAddress.TryGetValue(start, out var registered) && (CompareExchange(app) is not { } generic
                    || !registered.All(m => m == generic || m is ConcreteGenericMethodAnalysisContext { BaseMethodContext: var definition } && definition == generic)))
                return false;
            try
            {
                if (!app.Binary.TryMapVirtualAddressToRaw(start, out var raw) || raw < 0)
                    return false;
                var bytes = app.Binary.GetRawBinaryContent();
                if (raw > bytes.Length - HelperLength * 4)
                    return false;
                var words = new uint[HelperLength];
                for (var i = 0; i < words.Length; i++)
                    words[i] = BinaryPrimitives.ReadUInt32LittleEndian(bytes.Slice((int)raw + i * 4, 4));
                var keys = app.GetOrCreateKeyFunctionAddresses();
                var barrier = keys.il2cpp_codegen_write_barrier;
                // The barrier's own body may be a branch thunk, which then takes the same arguments.
                var barrierBodies = new HashSet<ulong>();
                var body = barrier;
                for (var hops = 0; body != 0 && hops < 4 && barrierBodies.Add(body); hops++)
                    body = NewArm64KeyFunctionAddresses.GetBranchThunkTarget(app, body);
                return barrier != 0 && IsReferenceCompareExchange(words, start,
                    target => barrierBodies.Contains(target) || keys.ResolveKeyFunctionAddress(target) == barrier);
            }
            catch (Exception)
            {
                return false; // An undecodable or out-of-range body is not proof.
            }
        });

    /// <summary>
    /// Matches the runtime's pointer compare-exchange:
    /// <code>
    /// stp x30, xR, [sp, #-16]!
    /// retry: ldaxr xA, [x0] / cmp xA, x2 / b.ne fail / stlxr wS, x1, [x0] / cbnz wS, retry / mov wF, #1 / b done
    /// fail:  clrex / mov wF, wzr
    /// done:  dmb ish / cmp wF, #0 / csel xR, x2, xA, ne / bl write_barrier / mov x0, xR / ldp x30, xR, [sp], #16 / ret
    /// </code>
    /// X0, X1 and X2 are never written, so the barrier sees the location and both outcomes return the
    /// value that was in memory: the comparand on success, where it equals the loaded value, else the load.
    /// </summary>
    internal static bool IsReferenceCompareExchange(uint[] w, ulong start, Func<ulong, bool> isWriteBarrier)
    {
        if (w.Length < HelperLength || (w[0] & 0xFFFF83FF) != 0xA9BF03FE) // STP X30, XR, [SP, #-16]!
            return false;
        var result = (int)((w[0] >> 10) & 31);
        if (result is < 19 or > 28 || (w[1] & 0xFFFFFFE0) != 0xC85FFC00) // LDAXR XA, [X0]
            return false;
        var loaded = (int)(w[1] & 31);
        if (loaded is 0 or 1 or 2 or 31 || loaded == result
            || w[2] != (0xEB02001Fu | (uint)loaded << 5) // CMP XA, X2
            || (w[3] & 0xFF00001F) != 0x54000001 || BranchIndex(w[3], 3) != 8 // B.NE fail
            || (w[4] & 0xFFE0FFFF) != 0xC800FC01) // STLXR WS, X1, [X0]
            return false;
        var status = (w[4] >> 16) & 31;
        if (status is 0 or 1 or 2 or 31
            || (w[5] & 0xFF00001F) != (0x35000000 | status) || BranchIndex(w[5], 5) != 1 // CBNZ WS, retry
            || (w[6] & 0xFFFFFFE0) != 0x52800020) // MOV WF, #1
            return false;
        var flag = w[6] & 31;
        return flag is not (0 or 1 or 2 or 31) && flag != loaded && flag != result
            && (w[7] & 0xFC000000) == 0x14000000 && (int)(w[7] << 6) >> 6 == 3 // B done
            && (w[8] & 0xFFFFF0FF) == 0xD503305F // CLREX
            && w[9] == (0x2A1F03E0 | flag) // MOV WF, WZR
            && w[10] == 0xD5033BBF // DMB ISH
            && w[11] == (0x7100001F | flag << 5) // CMP WF, #0
            && w[12] == (0x9A801040u | (uint)loaded << 16 | (uint)result) // CSEL XR, X2, XA, NE
            && (w[13] & 0xFC000000) == 0x94000000
            && isWriteBarrier(unchecked((ulong)((long)start + 13 * 4 + ((long)((int)(w[13] << 6) >> 6) << 2)))) // BL barrier
            && w[14] == (0xAA0003E0u | (uint)result << 16) // MOV X0, XR
            && w[15] == (0xA8C103FEu | (uint)result << 10) // LDP X30, XR, [SP], #16
            && w[16] == 0xD65F03C0; // RET
    }

    private static int BranchIndex(uint word, int index) => index + ((int)((word & 0x00FFFFE0) << 8) >> 13);
}
