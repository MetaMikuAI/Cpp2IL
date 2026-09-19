using System;

namespace Cpp2IL.Core.Model.Contexts;

/// <summary>
/// Why a method body had to fall back to a diagnostic stub for part of its code.
/// </summary>
/// <remarks>
/// IL generation degrades locally rather than failing the whole method: when it can't express
/// something in managed IL it emits a <c>NoteDecompilerIssue(...)</c> call and carries on. That
/// keeps the rest of the body, but it also means a "successful" method can be riddled with holes,
/// so each fallback records why it happened. Aggregating these is what turns "54% readable" into
/// an actionable list of what to fix.
/// </remarks>
public enum DegradationReason
{
    /// <summary>The instruction set lifter produced an explicit not-implemented placeholder.</summary>
    NotImplementedInstruction,

    /// <summary>The lifter marked the instruction invalid - usually a decode failure.</summary>
    InvalidInstruction,

    /// <summary>An ISIL opcode with no IL generation case at all.</summary>
    UnknownInstruction,

    /// <summary>A call to an address that resolved to neither a managed method nor a key function.</summary>
    MethodNotFound,

    /// <summary>A call whose target operand wasn't an address we could interpret.</summary>
    UnknownCallTarget,

    /// <summary>An instance call that arrived without a 'this' operand.</summary>
    MissingThisParameter,

    /// <summary>A call through a register/pointer that earlier passes failed to devirtualise.</summary>
    IndirectCall,

    /// <summary>A jump through a register/pointer that earlier passes failed to resolve.</summary>
    IndirectJump,

    /// <summary>A read from an address with no managed equivalent.</summary>
    UnmanagedMemoryLoad,

    /// <summary>An operand kind that <see cref="IlGenerator"/> can't load.</summary>
    UnknownOperandLoad,

    /// <summary>An operand kind that <see cref="IlGenerator"/> can't store into.</summary>
    UnknownOperandStore,

    /// <summary>A raw stack adjustment that stack analysis should have removed.</summary>
    UnresolvedStackShift,

    /// <summary>An SSA phi node that survived into IL generation.</summary>
    SurvivingPhiNode,

    /// <summary>A warning raised during analysis and replayed into the body.</summary>
    AnalysisWarning,
}

/// <summary>
/// A single IL generation fallback, with enough detail to aggregate across a whole run.
/// </summary>
/// <param name="Reason">The category, for grouping.</param>
/// <param name="Detail">
/// The distinguishing part within that category - an instruction mnemonic, an operand kind, etc.
/// Kept short and free of addresses so equal failures collapse onto one another when counted.
/// </param>
/// <param name="Address">
/// For <see cref="DegradationReason.MethodNotFound"/>, the unresolved call target. A handful of
/// addresses accounting for thousands of failures means one unrecognised runtime helper, not
/// thousands of separate problems.
/// </param>
public readonly record struct MethodDegradation(DegradationReason Reason, string Detail, ulong Address = 0)
{
    public override string ToString() => Address != 0
        ? $"{Reason} ({Detail}) @0x{Address:X}"
        : $"{Reason} ({Detail})";
}
