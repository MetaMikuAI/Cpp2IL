using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Text;
using System.Threading;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.OutputFormats;

/// <summary>
/// How a method body ended up, from most to least recovered.
/// </summary>
public enum MethodRecoveryOutcome
{
    /// <summary>Real IL, no fallbacks.</summary>
    Readable,

    /// <summary>Real IL, but with one or more <c>NoteDecompilerIssue</c> fallbacks in it.</summary>
    Degraded,

    /// <summary>Analysis threw; the body is a single <c>throw new Exception(detail)</c>.</summary>
    Failed,

    /// <summary>The declaring module is on the skip list (Unity/System/mscorlib).</summary>
    StubSkippedModule,

    /// <summary>The method's native code exceeded <see cref="MethodAnalysisContext.MaxMethodSizeBytes"/>.</summary>
    StubTooBig,

    /// <summary>
    /// There is no native code to recover - abstract methods, internal calls, and similar. These
    /// aren't failures, so they're excluded from the "reachable" denominator.
    /// </summary>
    StubNoNativeCode,
}

/// <summary>
/// Thread-safe tally of how a run's method bodies turned out, plus why the degraded ones degraded.
/// </summary>
/// <remarks>
/// Replaces the old success/total pair, which reported 100% on a run whose strict readability was
/// 54%: its denominator excluded every skipped module, and it counted a body stuffed with
/// <c>NoteDecompilerIssue</c> calls as a success. Optimisation work needs a number that moves when
/// the output actually improves, and a breakdown that says what to fix next.
/// </remarks>
public sealed class RecoveryStatistics
{
    // StubNoNativeCode is the last member; sizing off it avoids Enum.GetValues, which the
    // AOT analyser flags (IL3050) and which netstandard2.0 has no generic overload for.
    private readonly int[] _outcomes = new int[(int)MethodRecoveryOutcome.StubNoNativeCode + 1];
    private readonly ConcurrentDictionary<(DegradationReason Reason, string Detail), StrongBox<int>> _reasons = new();
    private readonly ConcurrentDictionary<(DegradationReason Reason, ulong Address), StrongBox<int>> _addresses = new();
    private readonly ConcurrentDictionary<string, (StrongBox<int> Total, StrongBox<int> Readable)> _perAssembly = new();

    public void Record(MethodRecoveryOutcome outcome, string assemblyName, IReadOnlyList<MethodDegradation>? degradations = null)
    {
        Interlocked.Increment(ref _outcomes[(int)outcome]);

        // Skipped modules never went through analysis, so ranking them against ones that did would
        // be misleading - leave them out of the per-assembly table.
        if (outcome != MethodRecoveryOutcome.StubSkippedModule)
        {
            var entry = _perAssembly.GetOrAdd(assemblyName, _ => (new StrongBox<int>(), new StrongBox<int>()));
            Interlocked.Increment(ref entry.Total.Value);
            if (outcome == MethodRecoveryOutcome.Readable)
                Interlocked.Increment(ref entry.Readable.Value);
        }

        if (degradations is null)
            return;

        foreach (var degradation in degradations)
        {
            var counter = _reasons.GetOrAdd((degradation.Reason, degradation.Detail), _ => new StrongBox<int>());
            Interlocked.Increment(ref counter.Value);

            if (degradation.Address != 0)
            {
                var addressCounter = _addresses.GetOrAdd((degradation.Reason, degradation.Address), _ => new StrongBox<int>());
                Interlocked.Increment(ref addressCounter.Value);
            }
        }
    }

    private int Count(MethodRecoveryOutcome outcome) => _outcomes[(int)outcome];

    /// <summary>
    /// Renders the tally. Returns an empty string when nothing was recorded, so output formats that
    /// only emit stubs print nothing rather than an empty table.
    /// </summary>
    public string BuildReport(int topN = 15)
    {
        var readable = Count(MethodRecoveryOutcome.Readable);
        var degraded = Count(MethodRecoveryOutcome.Degraded);
        var failed = Count(MethodRecoveryOutcome.Failed);
        var skipped = Count(MethodRecoveryOutcome.StubSkippedModule);
        var tooBig = Count(MethodRecoveryOutcome.StubTooBig);
        var noCode = Count(MethodRecoveryOutcome.StubNoNativeCode);

        var total = readable + degraded + failed + skipped + tooBig + noCode;
        if (total == 0)
            return string.Empty;

        // Methods with no native code can never be recovered, so a percentage that includes them
        // has a ceiling below 100 and can't be reasoned about. Report both.
        var reachable = total - noCode;

        var sb = new StringBuilder();
        sb.AppendLine();
        sb.AppendLine("=== Method recovery ===");
        sb.AppendLine($"  Readable           {readable,9:N0}  {Percent(readable, total),6:F2}%");
        sb.AppendLine($"  Degraded           {degraded,9:N0}  {Percent(degraded, total),6:F2}%");
        sb.AppendLine($"  Analysis failed    {failed,9:N0}  {Percent(failed, total),6:F2}%");
        sb.AppendLine($"  Stub (skipped)     {skipped,9:N0}  {Percent(skipped, total),6:F2}%");
        sb.AppendLine($"  Stub (too big)     {tooBig,9:N0}  {Percent(tooBig, total),6:F2}%");
        sb.AppendLine($"  Stub (no native)   {noCode,9:N0}  {Percent(noCode, total),6:F2}%");
        sb.AppendLine();
        sb.AppendLine($"  Strict readability : {Percent(readable, total):F2}%  ({readable:N0} / {total:N0})");
        sb.AppendLine($"  ... of reachable   : {Percent(readable, reachable):F2}%  ({readable:N0} / {reachable:N0}, excludes no-native-code)");

        AppendReasons(sb, topN, degraded);
        AppendAddresses(sb, topN);
        AppendWorstAssemblies(sb, topN);

        return sb.ToString();
    }

    private void AppendReasons(StringBuilder sb, int topN, int degraded)
    {
        if (_reasons.IsEmpty)
            return;

        var total = _reasons.Values.Sum(v => v.Value);
        sb.AppendLine();
        sb.AppendLine($"=== Top {topN} degradation reasons ({total:N0} across {degraded:N0} methods) ===");

        foreach (var ((reason, detail), count) in _reasons
                     .Select(kv => (kv.Key, kv.Value.Value))
                     .OrderByDescending(x => x.Value)
                     .Take(topN))
            sb.AppendLine($"  {count,8:N0}  {Percent(count, total),5:F1}%  {reason}: {detail}");
    }

    /// <summary>
    /// Lists the hottest addresses per reason. What the address means depends on the reason: an
    /// unresolved call target for <see cref="DegradationReason.MethodNotFound"/>, the containing
    /// method's entry point for the rest.
    /// </summary>
    private void AppendAddresses(StringBuilder sb, int topN)
    {
        foreach (var group in _addresses
                     .GroupBy(kv => kv.Key.Reason)
                     .OrderByDescending(g => g.Sum(kv => kv.Value.Value)))
        {
            var total = group.Sum(kv => kv.Value.Value);
            var distinct = group.Count();

            sb.AppendLine();
            sb.AppendLine($"=== Top {topN} addresses for {group.Key} ({total:N0} hits, {distinct:N0} distinct) ===");
            if (group.Key == DegradationReason.MethodNotFound)
                sb.AppendLine("    A few addresses covering most of these means one unrecognised runtime helper.");
            else
                sb.AppendLine("    Addresses are the entry points of the methods that hit this, for sampling.");

            foreach (var (address, count) in group
                         .Select(kv => (kv.Key.Address, kv.Value.Value))
                         .OrderByDescending(x => x.Value)
                         .Take(topN))
                sb.AppendLine($"  {count,8:N0}  {Percent(count, total),5:F1}%  0x{address:X}");
        }
    }

    private void AppendWorstAssemblies(StringBuilder sb, int topN, int minMethods = 200)
    {
        var ranked = _perAssembly
            .Select(kv => (Name: kv.Key, Total: kv.Value.Total.Value, Readable: kv.Value.Readable.Value))
            .Where(x => x.Total >= minMethods)
            .OrderBy(x => Percent(x.Readable, x.Total))
            .Take(topN)
            .ToList();

        if (ranked.Count == 0)
            return;

        sb.AppendLine();
        sb.AppendLine($"=== Least readable assemblies (>= {minMethods} analysed methods) ===");
        foreach (var (name, assemblyTotal, assemblyReadable) in ranked)
            sb.AppendLine($"  {Percent(assemblyReadable, assemblyTotal),6:F2}%  {assemblyReadable,7:N0}/{assemblyTotal,-7:N0}  {name}");
    }

    private static double Percent(int part, int whole) => whole == 0 ? 0 : part * 100.0 / whole;
}
