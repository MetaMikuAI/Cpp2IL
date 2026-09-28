using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// These Mono framework getters return the backing field directly. Recover reads
// in inlined caller code without changing field writes or managed addresses.
public static class CollectionFieldReadRecovery
{
    public static MethodAnalysisContext? TryGetGetter(FieldAnalysisContext field, MethodDefinition caller)
    {
        if (field.IsStatic)
            return null;

        var concrete = field as ConcreteGenericFieldAnalysisContext;
        var instance = concrete?.DeclaringType as GenericInstanceTypeAnalysisContext;
        var definition = concrete?.BaseFieldContext ?? field;
        var owner = definition.DeclaringType;
        var assemblyName = owner.FullName is "System.Collections.Generic.HashSet`1" or "System.Collections.Generic.HashSet`1+Enumerator"
            ? "System.Core" : "mscorlib";
        if (!owner.AppContext.AssembliesByName.TryGetValue(assemblyName, out var frameworkAssembly)
            || owner.DeclaringAssembly != frameworkAssembly
            || (definition.Attributes & FieldAttributes.FieldAccessMask) != FieldAttributes.Private)
            return null;

        var propertyName = (owner.FullName, definition.Name) switch
        {
            ("System.Collections.Generic.List`1", "_size") => "Count",
            ("System.Collections.Generic.List`1+Enumerator", "_current") => "Current",
            ("System.String", "_stringLength") => "Length",
            ("System.Nullable`1", "hasValue") => "HasValue",
            ("System.Collections.Generic.KeyValuePair`2", "key") => "Key",
            ("System.Collections.Generic.KeyValuePair`2", "value") => "Value",
            ("System.Collections.Generic.Dictionary`2+Enumerator", "_current") => "Current",
            ("System.Collections.Generic.Dictionary`2+KeyCollection+Enumerator", "_currentKey") => "Current",
            ("System.Collections.Generic.Dictionary`2+ValueCollection+Enumerator", "_currentValue") => "Current",
            ("System.Collections.Generic.Queue`1", "_size") => "Count",
            ("System.Collections.Generic.Stack`1", "_size") => "Count",
            ("System.Collections.Generic.HashSet`1", "_count") => "Count",
            ("System.Collections.Generic.HashSet`1+Enumerator", "_current") => "Current",
            _ => null,
        };
        if (propertyName == null || owner.GenericParameters.Count != 0 && instance?.GenericType != owner)
            return null;

        var getter = owner.Properties.SingleOrDefault(p => p.Name == propertyName)?.Getter;
        if (getter is not { IsStatic: false, Parameters.Count: 0, GenericParameters.Count: 0 }
            || getter.Visibility != MethodAttributes.Public || !SameType(getter.ReturnType, definition.FieldType)
            || getter.GetExtraData<MethodDefinition>("AsmResolverMethod") == caller)
            return null;

        return instance == null ? getter : new ConcreteGenericMethodAnalysisContext(getter, instance.GenericArguments, []);
    }

    private static bool SameType(TypeAnalysisContext left, TypeAnalysisContext right) => left == right
        || left is GenericInstanceTypeAnalysisContext l && right is GenericInstanceTypeAnalysisContext r
        && l.GenericType == r.GenericType && l.GenericArguments.SequenceEqual(r.GenericArguments);
}
