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
            }
        }

        // Indirect calls through a VirtualInvokeData returned by the interface-dispatch slow path:
        // call GetInterfaceInvokeDataFromVTableSlowPath(obj, interface, slot); call [result].
        // The call-site pattern (interface type + constant slot + result used as [x]) is specific
        // enough to resolve without identifying the slow path function itself.
        foreach (var block in method.ControlFlowGraph.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                if (instruction.OpCode == OpCode.IndirectCall)
                {
                    ResolveInterfaceSlowPathCall(method, instruction, definitions);
                    ResolveMethodInfoPointerCall(instruction, definitions);
                }
                else if (instruction.OpCode == OpCode.IndirectJump)
                {
                    ResolveMethodInfoPointerJump(method, instruction, block, definitions);
                }
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
    private static void ResolveMethodInfoPointerCall(Instruction dispatch, Dictionary<LocalVariable, Instruction> definitions)
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

        if (resolved.IsVoid)
            dispatch.RemoveOperandAt(1);

        dispatch.OpCode = resolved.IsVoid ? OpCode.CallVoid : OpCode.Call;
        dispatch.SetOperand(0, resolved);
        resolved.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(dispatch, resolved);
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
            return;

        // The InvokeData comes from the slow path call's return value, e.g.
        // Move invokeData_v, rax_v <- Call slowPath, rax_v, obj(rcx), interface(rdx), slot(r8), ...
        if (ChaseCopies(definitions, invokeData) is not { OpCode: OpCode.Call, Operands: [Immediate slowPathAddress, ..] } slowCall)
            return;

        // Only handle unresolved targets; a managed callee needs no recovery
        if (method.AppContext.MethodsByAddress.ContainsKey(slowPathAddress.UnsignedValue))
            return;

        if (slowCall.Operands.Count < 5)
            return;

        if (ChaseCopies(definitions, slowCall.Operands[3]) is not { OpCode: OpCode.Move, Operands: [_, TypeAnalysisContext declaringInterface] })
            return;

        if (declaringInterface is not (GenericInstanceTypeAnalysisContext { GenericType.IsInterface: true } or { IsInterface: true }))
            return;

        if (ChaseCopies(definitions, slowCall.Operands[4]) is not { OpCode: OpCode.Move, Operands: [_, Immediate slotImmediate] }
            || slotImmediate.Value is < 0 or > ushort.MaxValue)
            return;

        if (ResolveInterfaceSlot(declaringInterface, (int)slotImmediate.Value) is not { } resolved)
            return;

        // Kill the slow path call; its return value dies with the rewrite below
        slowCall.OpCode = OpCode.Nop;
        slowCall.SetOperands();

        if (resolved.IsVoid)
            dispatch.RemoveOperandAt(1);

        dispatch.OpCode = resolved.IsVoid ? OpCode.CallVoid : OpCode.Call;
        dispatch.SetOperand(0, resolved);
        resolved.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(dispatch, resolved);
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

        var scanLength = Math.Min(body.Count, 32);

        for (var i = 0; i < scanLength; i++)
        {
            var insn = body[i];

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
