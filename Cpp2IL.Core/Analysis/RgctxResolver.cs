using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Follows the runtime generic context chain and maps to actual values.
/// </summary>
public static class RgctxResolver
{
    public static bool Run(MethodAnalysisContext method)
    {
        var is32Bit = method.AppContext.Binary.is32Bit;
        var klassOffset = is32Bit ? 0x10 : 0x20;
        var rgctxOffset = is32Bit ? 0x60 : 0xC0;
        var methodRgctxOffset = is32Bit ? 0x1C : 0x38; // MethodInfo::rgctx_data
        var pointerSize = is32Bit ? 4 : 8;

        var definitions = method.ControlFlowGraph!.Instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());
        var changed = false;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Move || instruction.Operands.Count < 2)
                continue;

            if (instruction.Operands[0] is not LocalVariable destination)
                continue;

            if (instruction.Operands[1] is not MemoryOperand { Index: null, Scale: 0, Base: LocalVariable source } memory)
                continue;

            // Native code can keep &MethodInfo::klass in a register and dereference it later.
            // Follow SSA copies/constant additions without guessing the type of an interior pointer.
            var seen = new HashSet<LocalVariable>();
            var validAddress = true;
            while (definitions.TryGetValue(source, out var definition))
            {
                if (!seen.Add(source)) { validAddress = false; break; }
                if (definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable copied] })
                    source = copied;
                else if (definition is { OpCode: OpCode.Add, Operands: [_, LocalVariable origin, Immediate offset] })
                {
                    try { memory.Addend = checked(memory.Addend + offset.Value); }
                    catch (System.OverflowException) { validAddress = false; break; }
                    source = origin;
                }
                else break;
            }

            if (!validAddress) continue;

            var resolved = source.Type switch
            {
                // MethodInfo::klass - the instance the method belongs to, which is what carries the RGCTX
                RuntimeMethodInfoAnalysisContext info when memory.Addend == klassOffset && info.RepresentedMethod.DeclaringType is { } declaring
                    => new RuntimeClassTypeAnalysisContext(declaring, declaring.DeclaringAssembly),
                
                RuntimeMethodInfoAnalysisContext { RepresentedMethod: { } owningMethod } when memory.Addend == methodRgctxOffset && HasMethodRgctx(owningMethod)
                    => new MethodRgctxTableTypeAnalysisContext(owningMethod, owningMethod.CustomAttributeAssembly),

                RuntimeClassTypeAnalysisContext { RepresentedType: var owner } when memory.Addend == rgctxOffset
                    => new RgctxTableTypeAnalysisContext(owner, owner.DeclaringAssembly),

                RgctxTableTypeAnalysisContext table when memory.Addend % pointerSize == 0
                    => GetOrResolveEntry(table.ResolvedEntries, (int)(memory.Addend / pointerSize), () => ResolveTypeEntry(table.OwnerType, (int)(memory.Addend / pointerSize))),

                MethodRgctxTableTypeAnalysisContext table when memory.Addend % pointerSize == 0
                    => GetOrResolveEntry(table.ResolvedEntries, (int)(memory.Addend / pointerSize), () => ResolveMethodEntry(table.OwnerMethod, (int)(memory.Addend / pointerSize))),

                _ => null,
            };

            if (resolved == null)
                continue;

            // Wrappers are not unique objects, so compare what they contain, not references
            if (!DescribesSameThing(destination.Type, resolved))
                destination.Type = resolved;

            // The address read is meaningless in managed, so replace it
            instruction.SetOperand(1, resolved);
            changed = true;
        }

        return changed;
    }

    private static bool DescribesSameThing(TypeAnalysisContext? existing, TypeAnalysisContext candidate) =>
        (existing, candidate) switch
        {
            (RuntimeClassTypeAnalysisContext a, RuntimeClassTypeAnalysisContext b) => ReferenceEquals(a.RepresentedType, b.RepresentedType),
            (RgctxTableTypeAnalysisContext a, RgctxTableTypeAnalysisContext b) => ReferenceEquals(a.OwnerType, b.OwnerType),
            (MethodRgctxTableTypeAnalysisContext a, MethodRgctxTableTypeAnalysisContext b) => ReferenceEquals(a.OwnerMethod, b.OwnerMethod),
            _ => ReferenceEquals(existing, candidate),
        };

    private static TypeAnalysisContext? GetOrResolveEntry(Dictionary<int, TypeAnalysisContext?> cache, int index, System.Func<TypeAnalysisContext?> resolve)
    {
        if (cache.TryGetValue(index, out var cached))
            return cached;

        return cache[index] = resolve();
    }

    private static TypeAnalysisContext? ResolveTypeEntry(TypeAnalysisContext instance, int index)
    {
        var definition = (instance as GenericInstanceTypeAnalysisContext)?.GenericType ?? instance;

        if (definition.Definition is not { } typeDefinition)
            return null;

        // Open generic bodies still have a type context: their own formal parameters.
        IReadOnlyList<TypeAnalysisContext> typeArguments = instance is GenericInstanceTypeAnalysisContext concrete
            ? concrete.GenericArguments
            : definition.GenericParameters;

        return ResolveEntry(typeDefinition.RgctXs, index, typeArguments, [], instance.AppContext);
    }

    // Only a generic method (or one on a generic type) gets a per-method rgctx table
    private static bool HasMethodRgctx(MethodAnalysisContext method) => method switch
    {
        ConcreteGenericMethodAnalysisContext concrete => concrete.MethodGenericParameters.Count > 0,
        _ => method.GenericParameters.Count > 0 || method.DeclaringType?.GenericParameters.Count > 0,
    };

    private static TypeAnalysisContext? ResolveMethodEntry(MethodAnalysisContext owner, int index)
    {
        // an uninflated definition is shared generic code, so its own parameters stand in for the arguments
        if (owner is not ConcreteGenericMethodAnalysisContext concrete)
        {
            return owner.Definition is not { } ownDefinition
                ? null
                : ResolveEntry(ownDefinition.RgctXs, index, owner.DeclaringType?.GenericParameters ?? [], owner.GenericParameters, owner.AppContext);
        }

        if (concrete.IsPartialInstantiation || concrete.BaseMethodContext.Definition is not { } definition)
            return null;

        return ResolveEntry(definition.RgctXs, index, concrete.TypeGenericParameters, concrete.MethodGenericParameters, concrete.AppContext);
    }

    private static TypeAnalysisContext? ResolveEntry(Il2CppRGCTXDefinition[] entries, int index, IReadOnlyList<TypeAnalysisContext> typeArguments, IReadOnlyList<TypeAnalysisContext> methodArguments, ApplicationAnalysisContext appContext)
    {
        if (index < 0 || index >= entries.Length)
            return null;

        var entry = entries[index];

        // malformed/exotic metadata can make any of the lookups or inflations below throw, treat that as unresolvable
        try
        {
            switch (entry.type)
            {
                case Il2CppRGCTXDataType.IL2CPP_RGCTX_DATA_CLASS or Il2CppRGCTXDataType.IL2CPP_RGCTX_DATA_TYPE:
                {
                    var inflated = GenericInstantiation.Instantiate(appContext.ResolveIl2CppType(entry.Type), typeArguments, methodArguments);
                    return new RuntimeClassTypeAnalysisContext(inflated, inflated.DeclaringAssembly);
                }

                case Il2CppRGCTXDataType.IL2CPP_RGCTX_DATA_METHOD:
                {
                    var spec = entry.MethodSpec;

                    if (spec.MethodDefinition is not { } baseDefinition
                        || appContext.ResolveContextForMethod(baseDefinition) is not { DeclaringType: { } declaringType } baseContext)
                        return null;

                    var specTypeArguments = InflateAll(spec.GenericClassParams, typeArguments, methodArguments, appContext);
                    var specMethodArguments = InflateAll(spec.GenericMethodParams, typeArguments, methodArguments, appContext);

                    var inflatedMethod = specTypeArguments.Length == 0 && specMethodArguments.Length == 0
                        ? baseContext
                        : new ConcreteGenericMethodAnalysisContext(baseContext, specTypeArguments, specMethodArguments);

                    return new RuntimeMethodInfoAnalysisContext(inflatedMethod, declaringType.DeclaringAssembly);
                }

                // A constrained call (constrained. T callvirt M): the method T implements M with, as the
                // runtime picks it, or M itself when T is still a type parameter here.
                case Il2CppRGCTXDataType.IL2CPP_RGCTX_DATA_CONSTRAINED:
                {
                    var constrained = GenericInstantiation.Instantiate(appContext.ResolveIl2CppType(entry.Type), typeArguments, methodArguments);
                    if (MetadataUsage.DecodeMetadataUsage((uint)entry.MethodIndex, 0, appContext.LibCpp2IlContext) is not { Type: MetadataUsageType.MethodDef } usage
                        || appContext.ResolveContextForMethod(usage.AsMethod()) is not { } called)
                        return null;
                    var target = ImplementationOn(constrained, called) ?? called;
                    return new RuntimeMethodInfoAnalysisContext(target, (target.DeclaringType ?? constrained).DeclaringAssembly);
                }

                default:
                    return null;
            }
        }
        catch
        {
            return null;
        }
    }

    // The instance method of type (or a base) that implements or overrides called: same name, or an explicit
    // interface implementation of it, with as many parameters. Built for a generic instance.
    private static MethodAnalysisContext? ImplementationOn(TypeAnalysisContext type, MethodAnalysisContext called)
    {
        for (var current = type; current is not (null or GenericParameterTypeAnalysisContext); current = current.BaseType)
        {
            if (current == called.DeclaringType)
                return null;
            var instance = current as GenericInstanceTypeAnalysisContext;
            var definition = instance?.GenericType ?? current;
            if (definition.Methods.Where(m => !m.IsStatic && m.Parameters.Count == called.Parameters.Count
                    && (m.Name == called.Name || m.Name.EndsWith("." + called.Name))).ToList() is [{ } implementation])
                return instance == null ? implementation : new ConcreteGenericMethodAnalysisContext(implementation, instance.GenericArguments, []);
        }
        return null;
    }

    private static TypeAnalysisContext[] InflateAll(Il2CppType[] types, IReadOnlyList<TypeAnalysisContext> typeArguments, IReadOnlyList<TypeAnalysisContext> methodArguments, ApplicationAnalysisContext appContext)
    {
        var result = new TypeAnalysisContext[types.Length];

        for (var i = 0; i < types.Length; i++)
        {
            result[i] = GenericInstantiation.Instantiate(appContext.ResolveIl2CppType(types[i]), typeArguments, methodArguments);
        }

        return result;
    }
}
