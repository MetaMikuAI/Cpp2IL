using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using Iced.Intel;
using Instruction = Cpp2IL.Core.ISIL.Instruction;
using MemoryOperand = Cpp2IL.Core.ISIL.MemoryOperand;
using Register = Cpp2IL.Core.ISIL.Register;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Handles calls to internal il2cpp runtime helpers that are neither exports, key functions, nor
/// managed methods, and so would otherwise surface as "Method not found" diagnostics:
///
/// - The interface dispatch helpers (scan klass->interfaceOffsets for the interface, then tail-jmp
///   into the resolved method) are rewritten into direct calls to the interface method, using the
///   (slot, interface, this) arguments the caller sets up.
/// - The class-init fast path (checks Il2CppClass::cctor_finished and falls through to the slow
///   path) is excised entirely; static constructor guarantees have no IL-level representation.
/// - Calls into shared empty bodies (e.g. abstract/interface method stubs, System.Object::.ctor)
///   that ambiguity resolution failed to name are excised, since calling an empty body is a no-op.
/// </summary>
public static class RuntimeHelperRecovery
{
    // Il2CppClass_2 offsets on 64-bit metadata v27+ (no typeMetadataHandle in Il2CppClass_1)
    private const long CctorFinishedOffset64 = 0xD8;
    private const long CctorFinishedOrNoCctorOffset64 = 0xE0;
    private const long InterfaceOffsetsCountOffset64 = 0x12A;

    private enum HelperKind
    {
        NotAHelper,
        ClassInitCheck,
        InterfaceDispatch,
        EmptyBody,
        IsInst,
        InterlockedCmpxchg,
        ReferenceEquals,
        ReferenceNotEquals,
    }

    private static readonly ConcurrentDictionary<ulong, HelperKind> HelperKindCache = new();

    // Lazily resolved thunk-followed address of il2cpp_class_is_assignable_from's implementation.
    private static ulong _isAssignableFromImpl;

    public static void Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not X86InstructionSet || method.AppContext.Binary.is32Bit)
            return;

        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
            if (instruction.Destination is LocalVariable destination)
                definitions[destination] = instruction;

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (instruction.OpCode is not (OpCode.Call or OpCode.CallVoid))
                continue;

            if (instruction.Operands[0] is not Immediate target)
                continue;

            switch (Classify(method.AppContext, target.UnsignedValue))
            {
                case HelperKind.ClassInitCheck:
                    ExciseClassInitCheck(instruction);
                    break;
                case HelperKind.EmptyBody:
                    ExciseEmptyBodyCall(instruction);
                    break;
                case HelperKind.InterfaceDispatch:
                    ResolveInterfaceDispatch(method, instruction, definitions);
                    break;
                case HelperKind.IsInst:
                    RewriteIsInst(instruction, definitions);
                    break;
                case HelperKind.InterlockedCmpxchg:
                    RewriteCompareExchange(method, instruction);
                    break;
                case HelperKind.ReferenceEquals:
                    RewriteReferenceCompare(instruction, OpCode.CheckEqual);
                    break;
                case HelperKind.ReferenceNotEquals:
                    RewriteReferenceCompare(instruction, OpCode.CheckNotEqual);
                    break;
            }
        }

        // Indirect calls through a VirtualInvokeData returned by the interface-dispatch slow path:
        // call GetInterfaceInvokeDataFromVTableSlowPath(obj, interface, slot); call [result].
        // The call-site pattern (interface type + constant slot + result used as [x]) is specific
        // enough to resolve without identifying the slow path function itself.
        // Snapshot first: tail-call rewriting appends a Return to the block, which would
        // otherwise modify the collection being enumerated.
        var indirectDispatches = method.ControlFlowGraph.Blocks
            .SelectMany(block => block.Instructions.Select(instruction => (block, instruction)))
            .Where(pair => pair.instruction.OpCode is OpCode.IndirectCall or OpCode.IndirectJump)
            .ToList();

        foreach (var (block, instruction) in indirectDispatches)
        {
            if (instruction.OpCode == OpCode.IndirectCall)
            {
                ResolveInterfaceSlowPathCall(method, instruction, definitions);
                ResolveMethodInfoPointerCall(method, instruction, definitions);
            }
            else
            {
                ResolveMethodInfoPointerJump(method, instruction, block, definitions);
            }
        }
    }

    // A tail call (jmp) through a MethodInfo pointer: rewrite to a regular call followed by a return.
    private static void ResolveMethodInfoPointerJump(MethodAnalysisContext method, Instruction dispatch, Graphs.Block block, Dictionary<LocalVariable, Instruction> definitions)
    {
        var pointerLoad = dispatch.Operands[0] switch
        {
            MemoryOperand { Index: null, Scale: 0, Addend: 0 or 8 or 0x10, Base: LocalVariable memoryBase } => memoryBase,
            LocalVariable target => ChaseCopies(definitions, target) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Addend: 0 or 8 or 0x10, Base: LocalVariable chaseBase }] }
                ? chaseBase
                : null,
            _ => null,
        };

        if (pointerLoad?.Type is not RuntimeMethodInfoAnalysisContext { RepresentedMethod: { } resolved })
            return;

        var callingConventions = resolved.AppContext.InstructionSet.CallingConventionResolver;

        // an IndirectJump's return register operand is a stale use rather than a return slot, so rebuild from scratch
        var operands = new List<IOperand> { resolved };

        if (!resolved.IsVoid)
            operands.Add(new LocalVariable("methodInfoTailCallResult", callingConventions?.ReturnRegister(resolved) ?? new Register(null, "rax")));

        operands.AddRange(dispatch.Operands.Skip(2));

        dispatch.SetOperands(operands);
        dispatch.OpCode = resolved.IsVoid ? OpCode.CallVoid : OpCode.Call;
        callingConventions?.RemapRawArguments(dispatch, resolved);

        var returnOperands = !method.IsVoid && !resolved.IsVoid
            ? new List<IOperand> { dispatch.Operands[1] }
            : [];

        block.AddInstruction(new Instruction(-1, OpCode.Return, returnOperands));
        block.CalculateBlockType();
    }

    // Shared generic code invokes methods via MethodInfo: methodPointer (+0), virtualMethodPointer
    // (+8) for virtual dispatch, and invoker_method (+0x10) for generic instances. The MethodInfo
    // local already names the method in every case.
    private static void ResolveMethodInfoPointerCall(MethodAnalysisContext method, Instruction dispatch, Dictionary<LocalVariable, Instruction> definitions)
    {
        var pointerLoad = dispatch.Operands[0] switch
        {
            MemoryOperand { Index: null, Scale: 0, Addend: 0 or 8 or 0x10, Base: LocalVariable memoryBase } => memoryBase,
            LocalVariable target => ChaseCopies(definitions, target) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Addend: 0 or 8 or 0x10, Base: LocalVariable chaseBase }] }
                ? chaseBase
                : null,
            _ => null,
        };

        if (pointerLoad?.Type is not RuntimeMethodInfoAnalysisContext { RepresentedMethod: { } resolved })
            return;

        // A large-struct callee reads its return buffer from rcx. That slot is dropped by
        // RemapRawArguments, so type the stack slot it points at now.
        TypeHiddenReturnBuffer(method, dispatch, definitions, resolved);

        if (resolved.IsVoid)
            dispatch.RemoveOperandAt(1);

        dispatch.OpCode = resolved.IsVoid ? OpCode.CallVoid : OpCode.Call;
        dispatch.SetOperand(0, resolved);
        resolved.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(dispatch, resolved);
    }

    // rcx (operand slot 2 on a raw-layout call) may carry lea rsp+N for the hidden return buffer.
    // Resolve that to the named stack slot and give it the callee's return type.
    private static void TypeHiddenReturnBuffer(MethodAnalysisContext method, Instruction dispatch, Dictionary<LocalVariable, Instruction> definitions, MethodAnalysisContext resolved)
    {
        if (resolved.AppContext.InstructionSet.CallingConventionResolver?.ReturnsViaHiddenBuffer(resolved) != true
            || resolved.ReturnType == method.AppContext.SystemTypes.SystemVoidType)
            return;

        if (dispatch.Operands.Count <= 2 || dispatch.Operands[2] is not LocalVariable rcxLocal)
            return;

        if (!definitions.TryGetValue(rcxLocal, out var rcxDefinition)
            || rcxDefinition is not { OpCode: OpCode.Add or OpCode.Subtract, Operands: [_, { } rspSource, Immediate offset] }
            || rspSource is not LocalVariable { Register.Name: "rsp" })
            return;

        var slotOffset = rcxDefinition.OpCode == OpCode.Add ? offset.Value : -offset.Value;
        var slot = method.Locals.FirstOrDefault(l => l.Register.Name == $"stack_{Math.Abs(slotOffset):X}");

        if (slot is { Type: null })
            slot.Type = resolved.ReturnType;
    }

    private static void ResolveInterfaceSlowPathCall(MethodAnalysisContext method, Instruction dispatch, Dictionary<LocalVariable, Instruction> definitions)
    {
        // The dispatched address is [invokeData + 0] (VirtualInvokeData::methodPtr)
        var invokeData = dispatch.Operands[0] switch
        {
            MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable memoryBase } => memoryBase,
            LocalVariable target => ChaseCopies(definitions, target) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable chaseBase }] }
                ? chaseBase
                : null,
            _ => null,
        };

        if (invokeData == null)
        {
            return;
        }

        // The InvokeData comes from the slow path call's return value, e.g.
        // Move invokeData_v, rax_v <- Call slowPath, rax_v, obj(rcx), interface(rdx), slot(r8), ...
        // With the fast path inlined, the merge block holds a phi(fastEntry, slowCallResult)
        // instead - the slow call is then one of the phi's inputs.
        var invokeDataDef = ChaseCopies(definitions, invokeData);

        Instruction? slowCall = null;
        Immediate? slowPathAddress = null;

        if (invokeDataDef is { OpCode: OpCode.Call, Operands: [Immediate directAddress, ..] })
        {
            slowCall = invokeDataDef;
            slowPathAddress = directAddress;
        }
        else if (invokeDataDef is { OpCode: OpCode.Phi })
        {
            foreach (var phiOperand in invokeDataDef.Operands.Skip(1))
            {
                if (phiOperand is not LocalVariable phiLocal
                    || ChaseCopies(definitions, phiLocal) is not { OpCode: OpCode.Call, Operands: [Immediate phiAddress, ..] } candidate)
                    continue;

                slowCall = candidate;
                slowPathAddress = phiAddress;
                break;
            }
        }

        if (slowCall == null || slowPathAddress == null)
        {
            return;
        }

        // Only handle unresolved targets; a managed callee needs no recovery
        if (method.AppContext.MethodsByAddress.ContainsKey(slowPathAddress.Value.UnsignedValue))
        {
            return;
        }

        if (slowCall.Operands.Count < 5)
        {
            return;
        }

        // interface argument (rdx): either a direct typeof operand or a local holding one
        var declaringInterface = slowCall.Operands[3] switch
        {
            TypeAnalysisContext direct => direct,
            LocalVariable interfaceLocal when ChaseCopies(definitions, interfaceLocal) is { OpCode: OpCode.Move, Operands: [_, TypeAnalysisContext loaded] } => loaded,
            _ => null,
        };

        if (declaringInterface == null)
        {
            return;
        }

        if (declaringInterface is not (GenericInstanceTypeAnalysisContext { GenericType.IsInterface: true } or { IsInterface: true }))
        {
            return;
        }

        // slot argument (r8): usually a literal 0/N, directly or via a local
        var slotValue = slowCall.Operands[4] switch
        {
            Immediate directImm => (long?)directImm.Value,
            LocalVariable slotLocal when ChaseCopies(definitions, slotLocal) is { OpCode: OpCode.Move, Operands: [_, Immediate loadedImm] } => loadedImm.Value,
            _ => null,
        };

        if (slotValue is not { } slot || slot is < 0 or > ushort.MaxValue)
        {
            return;
        }

        if (ResolveInterfaceSlot(declaringInterface, (int)slot) is not { } resolved)
        {
            return;
        }

        // Kill the slow path call; its return value dies with the rewrite below
        slowCall.OpCode = OpCode.Nop;
        slowCall.SetOperands();

        if (resolved.IsVoid)
            dispatch.RemoveOperandAt(1);

        dispatch.OpCode = resolved.IsVoid ? OpCode.CallVoid : OpCode.Call;
        dispatch.SetOperand(0, resolved);
        resolved.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(dispatch, resolved);
    }

    // cmp rcx, rdx; setne|sete al; (movzx eax, al;) ret - optionally with a not after the set.
    private static bool IsReferenceCompare(InstructionList body, out bool isEquality)
    {
        isEquality = false;

        if (body.Count < 3)
            return false;

        if (body[0].Mnemonic != Mnemonic.Cmp
            || body[0].Op0Kind != OpKind.Register || body[0].Op0Register != Iced.Intel.Register.RCX
            || body[0].Op1Kind != OpKind.Register || body[0].Op1Register != Iced.Intel.Register.RDX)
            return false;

        var index = 1;

        // setne (a != b) or sete (a == b); setne is the common form
        if (body[index].Mnemonic == Mnemonic.Setne)
            isEquality = false;
        else if (body[index].Mnemonic == Mnemonic.Sete)
            isEquality = true;
        else
            return false;

        if (body[index].Op0Kind != OpKind.Register || body[index].Op0Register != Iced.Intel.Register.AL)
            return false;

        index++;

        // optional: movzx eax, al
        if (index < body.Count && body[index].Mnemonic == Mnemonic.Movzx
            && body[index].Op0Kind == OpKind.Register && body[index].Op0Register == Iced.Intel.Register.EAX)
            index++;

        return index < body.Count && body[index].Mnemonic == Mnemonic.Ret;
    }

    // a != b / a == b as a comparison instruction instead of a call.
    private static void RewriteReferenceCompare(Instruction call, OpCode comparison)
    {
        if (call.OpCode != OpCode.Call || call.Operands.Count < 4)
            return;

        call.OpCode = comparison;
        call.SetOperands(call.Operands[1], call.Operands[2], call.Operands[3]);
    }

    private static HelperKind Classify(ApplicationAnalysisContext appContext, ulong address)
        => HelperKindCache.GetOrAdd(address, addr => ClassifyUncached(appContext, addr));

    // il2cpp_codegen_* helpers are reached through bare jmp thunks; follow them to the real body.
    private static ulong FollowThunks(ApplicationAnalysisContext appContext, ulong address)
    {
        var visited = new HashSet<ulong>();

        while (visited.Add(address))
        {
            var target = appContext.InstructionSet.GetThunkTarget(appContext, address);
            if (target == 0)
                return address;

            address = target;
        }

        return address;
    }

    private static HelperKind ClassifyUncached(ApplicationAnalysisContext appContext, ulong address)
    {
        var resolved = FollowThunks(appContext, address);

        if (IsIsInstImplementation(appContext, resolved))
            return HelperKind.IsInst;

        InstructionList body;
        try
        {
            body = X86Utils.GetMethodBodyAtVirtAddressNew(resolved, true, appContext.Binary);
        }
        catch
        {
            return HelperKind.NotAHelper;
        }

        if (body.Count == 0)
            return HelperKind.NotAHelper;

        // Shared empty body: a bare ret (possibly with stack cleanup), used for abstract/interface
        // stubs such as System.Object::.ctor.
        if (body[0].Mnemonic == Mnemonic.Ret)
            return HelperKind.EmptyBody;

        // Reference comparison helper (object.ReferenceEquals / record op_Inequality shared
        // bodies): cmp rcx, rdx; setne|sete al; ret - the call is just a != b / a == b.
        if (IsReferenceCompare(body, out var isEquality))
            return isEquality ? HelperKind.ReferenceEquals : HelperKind.ReferenceNotEquals;

        var scanLength = Math.Min(body.Count, 32);

        for (var i = 0; i < scanLength; i++)
        {
            var insn = body[i];

            // Interlocked.CompareExchange implementation: a lock-prefixed cmpxchg
            if (insn.Mnemonic == Mnemonic.Cmpxchg && insn.HasLockPrefix)
                return HelperKind.InterlockedCmpxchg;

            // Interface dispatch helper: movzx rXX, word [klass + interface_offsets_count]
            if (insn.Mnemonic == Mnemonic.Movzx
                && insn.Op1Kind == OpKind.Memory
                && insn.MemorySize == MemorySize.UInt16
                && insn.MemoryDisplacement64 == InterfaceOffsetsCountOffset64)
                return HelperKind.InterfaceDispatch;

            // Class-init fast path: cmp dword [klass + cctor_finished (or _or_no_cctor)], 0
            if (insn.Mnemonic == Mnemonic.Cmp
                && insn.Op0Kind == OpKind.Memory
                && insn.MemorySize == MemorySize.UInt32
                && insn.MemoryDisplacement64 is CctorFinishedOffset64 or CctorFinishedOrNoCctorOffset64
                && insn.Op1Kind.IsImmediate() && insn.GetImmediate(1) == 0)
                return HelperKind.ClassInitCheck;
        }

        return HelperKind.NotAHelper;
    }

    private static ulong GetIsAssignableFromImpl(ApplicationAnalysisContext appContext)
    {
        if (_isAssignableFromImpl != 0)
            return _isAssignableFromImpl;

        var export = appContext.Binary.GetVirtualAddressOfExportedFunctionByName("il2cpp_class_is_assignable_from");

        return _isAssignableFromImpl = export == 0 ? 0 : FollowThunks(appContext, export);
    }

    // il2cpp_codegen_isinst / vm::Type::IsInst: null-checks the object, calls
    // il2cpp_class_is_assignable_from, then branches on its boolean result to yield obj-or-null.
    private static bool IsIsInstImplementation(ApplicationAnalysisContext appContext, ulong address)
    {
        var impl = GetIsAssignableFromImpl(appContext);

        if (impl == 0)
            return false;

        InstructionList body;
        try
        {
            body = X86Utils.GetMethodBodyAtVirtAddressNew(address, true, appContext.Binary);
        }
        catch
        {
            return false;
        }

        var callsAssignableFrom = false;
        var testsResult = false;

        foreach (var insn in body)
        {
            if (insn.Mnemonic == Mnemonic.Call && insn.Op0Kind == OpKind.NearBranch64
                && FollowThunks(appContext, insn.NearBranchTarget) == impl)
                callsAssignableFrom = true;

            if (insn.Mnemonic == Mnemonic.Test && insn.Op0Kind == OpKind.Register
                && insn.Op0Register == Iced.Intel.Register.AL && insn.Op1Register == Iced.Intel.Register.AL)
                testsResult = true;
        }

        return callsAssignableFrom && testsResult;
    }

    // A lock cmpxchg [rcx], rdx with the new value in r8 is Interlocked.CompareExchange<T>'s
    // shared body: (ref T location, T value, T comparand), old value returned in rax. The class
    // form (reference types) is what gets called through wrappers and inlined into collections.
    private static void RewriteCompareExchange(MethodAnalysisContext method, Instruction call)
    {
        if (call.OpCode != OpCode.Call || call.Operands.Count < 5)
            return;

        if (GetCompareExchangeMethod(method.AppContext) is not { } resolved)
            return;

        // unmanaged layout: [target, ret, rcx(ref), rdx(value), r8(comparand), ...]
        call.SetOperands(resolved, call.Operands[1], call.Operands[2], call.Operands[3], call.Operands[4]);
    }

    private static MethodAnalysisContext? _compareExchange;

    private static MethodAnalysisContext? GetCompareExchangeMethod(ApplicationAnalysisContext appContext)
    {
        if (_compareExchange != null)
            return _compareExchange;

        foreach (var assembly in appContext.Assemblies)
        {
            var interlocked = assembly.Types.FirstOrDefault(t => t.FullName == "System.Threading.Interlocked");
            var cmpxchg = interlocked?.Methods.FirstOrDefault(m => m.Name == "CompareExchange" && m.GenericParameters.Count == 1);

            if (cmpxchg == null)
                continue;

            return _compareExchange = new ConcreteGenericMethodAnalysisContext(cmpxchg, [], [appContext.SystemTypes.SystemObjectType]);
        }

        return null;
    }

    // isinst(obj, klass) has the managed layout (obj in rcx, type token in rdx), returning
    // obj-or-null in rax. The type token arrives as a metadata-usage global load, already resolved
    // to a TypeAnalysisContext by this point.
    private static void RewriteIsInst(Instruction call, Dictionary<LocalVariable, Instruction> definitions)
    {
        if (call.OpCode != OpCode.Call || call.Operands.Count < 4)
            return;

        var result = call.Operands[1];
        var testedObject = call.Operands[2]; // rcx

        if (ChaseCopies(definitions, call.Operands[3]) is not { OpCode: OpCode.Move, Operands: [_, TypeAnalysisContext castType] })
            return;

        call.OpCode = OpCode.IsInst;
        call.SetOperands(result, testedObject, castType);
    }

    // The fast path returns its klass argument unchanged, so a non-void call degrades to a copy of
    // the klass local rather than being dropped outright.
    private static void ExciseClassInitCheck(Instruction call)
    {
        if (call.OpCode == OpCode.Call && call.Operands.Count >= 3)
        {
            call.OpCode = OpCode.Move;
            call.SetOperands(call.Operands[1], call.Operands[2]);
        }
        else
        {
            call.OpCode = OpCode.Nop;
            call.SetOperands();
        }
    }

    private static void ExciseEmptyBodyCall(Instruction call)
    {
        if (call.OpCode == OpCode.Call && call.Operands.Count >= 2)
        {
            // The stub returns whatever was in rax; a zero is at least a defined value.
            call.OpCode = OpCode.Move;
            call.SetOperands(call.Operands[1], new Immediate(0));
        }
        else
        {
            call.OpCode = OpCode.Nop;
            call.SetOperands();
        }
    }

    // The helpers take (slot in rcx, interface Il2CppClass* in rdx, this in r8) and tail-jmp into
    // the resolved method, so the call site is equivalent to directly calling the interface method.
    private static void ResolveInterfaceDispatch(MethodAnalysisContext method, Instruction call, Dictionary<LocalVariable, Instruction> definitions)
    {
        var argBase = call.OpCode == OpCode.Call ? 2 : 1;

        // rcx, rdx, r8 for an unmanaged-layout call
        if (call.Operands.Count < argBase + 3)
            return;

        if (ChaseCopies(definitions, call.Operands[argBase]) is not { OpCode: OpCode.Move, Operands: [_, Immediate slotImmediate] }
            || slotImmediate.Value is < 0 or > ushort.MaxValue)
            return;

        if (ChaseCopies(definitions, call.Operands[argBase + 1]) is not { OpCode: OpCode.Move, Operands: [_, TypeAnalysisContext declaringInterface] })
            return;

        if (declaringInterface is not (GenericInstanceTypeAnalysisContext { GenericType.IsInterface: true } or { IsInterface: true }))
            return;

        if (call.Operands[argBase + 2] is not LocalVariable thisLocal)
            return;

        var resolved = ResolveInterfaceSlot(declaringInterface, (int)slotImmediate.Value);

        // The helper's own arguments occupy rcx/rdx/r8, so at most one real argument (r9) can
        // be passed through to the target method.
        if (resolved == null || resolved.Parameters.Count > 1)
            return;

        var extraArgs = new List<IOperand>();
        if (resolved.Parameters.Count == 1)
        {
            if (call.Operands.Count < argBase + 4)
                return;

            extraArgs.Add(call.Operands[argBase + 3]); // r9
        }

        if (resolved.IsVoid)
        {
            // the lifter emits even void-targeting unknown calls as Call with an unused rax result
            if (call.OpCode == OpCode.Call)
                call.RemoveOperandAt(1);

            call.SetOperands([resolved, thisLocal, .. extraArgs]);
        }
        else if (call.OpCode == OpCode.Call)
        {
            call.SetOperands([resolved, call.Operands[1], thisLocal, .. extraArgs]);
        }
        else
            return; // return-value shape mismatch, leave it alone

        call.OpCode = resolved.IsVoid ? OpCode.CallVoid : OpCode.Call;
    }

    private static MethodAnalysisContext? ResolveInterfaceSlot(TypeAnalysisContext declaringInterface, int slot)
    {
        if (declaringInterface is GenericInstanceTypeAnalysisContext genericInstance)
        {
            var baseMethod = genericInstance.GenericType.Methods.FirstOrDefault(m => m.Definition?.slot == slot);
            return baseMethod == null ? null : new ConcreteGenericMethodAnalysisContext(baseMethod, genericInstance.GenericArguments, []);
        }

        return declaringInterface.Methods.FirstOrDefault(m => m.Definition?.slot == slot);
    }

    private static Instruction? ChaseCopies(Dictionary<LocalVariable, Instruction> definitions, IOperand operand)
    {
        if (operand is not LocalVariable local)
            return null;

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
