using System;
using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.Elf;

namespace Cpp2IL.Core.Analysis;

// Restore only nested, single-normal-path resource lifetimes whose native managed
// exception paths have been proved to dispose the same resources in the same order.
internal sealed class UsingRecovery
{
    private sealed record Scope(Instruction Allocation, Instruction Constructor, NativeDisposal Disposal);
    private readonly List<Instruction> _trace;
    private readonly List<Scope> _scopes;
    private UsingRecovery(List<Instruction> trace, List<Scope> scopes) { _trace = trace; _scopes = scopes; }

    internal static UsingRecovery? Prepare(MethodAnalysisContext method)
    {
        if (method.NativeDisposals.Count == 0 || method.AppContext.Binary is not ElfFile binary
            || method.AppContext.InstructionSet is not NewArmV8InstructionSet) return null;
        try { return PrepareCore(method, binary); }
        catch (Exception e) when (e is ArgumentException or InvalidOperationException or OverflowException or IndexOutOfRangeException)
        { return null; }
    }

    private static UsingRecovery? PrepareCore(MethodAnalysisContext method, ElfFile binary)
    {
        var graph = method.ControlFlowGraph!;
        var all = graph.Instructions;
        var definitions = all.Where(i => i.Destination is LocalVariable).GroupBy(i => (LocalVariable)i.Destination!)
            .Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
        var allocations = definitions.Where(kv => kv.Value.OpCode == OpCode.Newobj && kv.Key.Type is { IsValueType: false }).ToDictionary();
        var trace = new List<Instruction>();
        var visited = new HashSet<Block>();
        var acquired = new HashSet<LocalVariable>();
        var block = graph.EntryBlock;
        while (block != graph.ExitBlock)
        {
            if (!visited.Add(block)) return null;
            foreach (var instruction in block.Instructions)
            {
                if (instruction.OpCode is OpCode.Invalid or OpCode.IndirectCall or OpCode.IndirectJump or OpCode.Switch or OpCode.Throw) return null;
                trace.Add(instruction);
                if (instruction is { OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: ".ctor" }, LocalVariable receiver, ..] }
                    && allocations.ContainsKey(receiver)) acquired.Add(receiver);
            }
            if (block.Successors.Count == 1) { block = block.Successors[0]; continue; }
            if (block.Successors.Count != 2
                || block.Instructions.LastOrDefault() is not { OpCode: OpCode.ConditionalJump, Operands: [var target, LocalVariable condition] }
                || !definitions.TryGetValue(condition, out var comparison)
                || comparison is not { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, LocalVariable obj, Immediate { Value: 0 }] }
                || !acquired.Contains(obj)) return null;
            var taken = target as Block ?? (target is Instruction targetInstruction ? graph.FindBlockByInstruction(targetInstruction) : null);
            if (taken == null || !block.Successors.Contains(taken)) return null;
            block = comparison.OpCode == OpCode.CheckNotEqual ? taken : block.Successors.Single(s => s != taken);
        }
        if (trace.LastOrDefault()?.OpCode != OpCode.Return) return null;
        var scopes = new List<Scope>();
        foreach (var disposal in method.NativeDisposals.Where(d => trace.Contains(d.Call)))
        {
            if (disposal.Call is not { OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext, LocalVariable receiver] }
                || !allocations.TryGetValue(receiver, out var allocation)
                || IlGenerator.FindConstructorCall(method, allocation) is not { NativeAddress: not 0 } constructor
                || !trace.Contains(allocation) || !trace.Contains(constructor)
                || constructor.NativeAddress >= disposal.Call.NativeAddress || allocation.NativeAddress >= constructor.NativeAddress
                || !ImplementsDisposable(receiver.Type!)) return null;
            scopes.Add(new Scope(allocation, constructor, disposal));
        }
        if (scopes.Count == 0 || scopes.Select(s => s.Allocation).Distinct().Count() != scopes.Count) return null;
        var active = new Stack<Scope>();
        foreach (var instruction in trace)
        {
            if (scopes.Find(s => s.Disposal.Call == instruction) is { } ending)
            { if (!active.TryPop(out var last) || last != ending) return null; }
            if (scopes.Find(s => s.Constructor == instruction) is { } starting) active.Push(starting);
        }
        if (active.Count != 0) return null;
        var table = ElfExceptionTable.Read(binary, method.UnderlyingPointer, method.RawBytes.Length);
        if (table == null) return null;
        var proof = new Arm64CleanupProof(method, table);
        List<NativeDisposal> Expected(ulong pc) => scopes.Where(s => s.Constructor.NativeAddress < pc && pc < s.Disposal.Call.NativeAddress)
            .OrderByDescending(s => s.Constructor.NativeAddress).Select(s => s.Disposal).ToList();
        foreach (var instruction in trace.Where(i => i.IsCall || i.OpCode == OpCode.Newobj))
        {
            if (instruction.NativeAddress == 0 || !proof.Proves(instruction.NativeAddress, Expected(instruction.NativeAddress))) return null;
        }
        var throws = method.ConvertedIsil!.Where(i => i.OpCode == OpCode.Throw && i.NativeAddress != 0).Select(i => i.NativeAddress).ToHashSet();
        foreach (var (branch, throwing) in proof.OutlinedThrows(throws))
        {
            var expected = Expected(branch);
            if (expected.Count > 0 && !proof.Proves(throwing, expected)) return null;
        }
        return new UsingRecovery(trace, scopes);
    }

    private static bool ImplementsDisposable(TypeAnalysisContext type)
    {
        var seen = new HashSet<TypeAnalysisContext>();
        for (var current = type; current != null && seen.Add(current); current = current.BaseType)
            if (current.InterfaceContexts.Any(i => i.FullName == "System.IDisposable")) return true;
        return false;
    }

    internal void Apply(MethodDefinition method, Dictionary<Instruction, List<CilInstruction>> map)
    {
        var body = method.CilMethodBody!;
        if (body.ExceptionHandlers.Count != 0) return;
        var output = new List<CilInstruction>();
        var starts = new Dictionary<Scope, CilInstruction>();
        var handlers = new List<CilExceptionHandler>();
        foreach (var instruction in _trace)
        {
            if (instruction.OpCode is OpCode.Jump or OpCode.ConditionalJump) continue;
            if (!map.TryGetValue(instruction, out var generated)) return;
            if (_scopes.Find(s => s.Disposal.Call == instruction) is { } scope)
            {
                if (!starts.TryGetValue(scope, out var start) || generated.Count == 0) return;
                var continuation = new CilInstruction(CilOpCodes.Nop);
                output.Add(new CilInstruction(CilOpCodes.Leave, new CilInstructionLabel(continuation)));
                output.AddRange(generated);
                output.Add(new CilInstruction(CilOpCodes.Endfinally));
                output.Add(continuation);
                handlers.Add(new CilExceptionHandler
                {
                    HandlerType = CilExceptionHandlerType.Finally,
                    TryStart = new CilInstructionLabel(start), TryEnd = new CilInstructionLabel(generated[0]),
                    HandlerStart = new CilInstructionLabel(generated[0]), HandlerEnd = new CilInstructionLabel(continuation),
                });
            }
            else
            {
                output.AddRange(generated);
                if (_scopes.Find(s => s.Allocation == instruction) is { } allocated)
                {
                    // The fused newobj includes the constructor; failure must not dispose this object.
                    if (!generated.Any(i => i.OpCode.Code == CilCode.Newobj)) return;
                    var start = new CilInstruction(CilOpCodes.Nop);
                    output.Add(start); starts.Add(allocated, start);
                }
            }
        }
        // Instruction maps must not hide internal branches that would bypass a handler.
        if (output.Any(i => i.OpCode.FlowControl is CilFlowControl.Branch or CilFlowControl.ConditionalBranch
            && i.OpCode.Code != CilCode.Leave)) return;
        body.Instructions.Clear();
        foreach (var instruction in output) body.Instructions.Add(instruction);
        foreach (var handler in handlers) body.ExceptionHandlers.Add(handler);
    }
}
