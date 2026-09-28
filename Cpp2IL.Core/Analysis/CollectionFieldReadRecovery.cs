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
        if (owner.DeclaringAssembly != owner.AppContext.SystemTypes.SystemObjectType.DeclaringAssembly
            || owner.DeclaringAssembly.Name != "mscorlib"
            || (definition.Attributes & FieldAttributes.FieldAccessMask) != FieldAttributes.Private)
            return null;

        var propertyName = (owner.FullName, definition.Name) switch
        {
            ("System.Collections.Generic.List`1", "_size") => "Count",
            ("System.Collections.Generic.List`1+Enumerator", "_current") => "Current",
            ("System.String", "_stringLength") => "Length",
            ("System.Nullable`1", "hasValue") => "HasValue",
            _ => null,
        };
        if (propertyName == null || owner.GenericParameters.Count != 0 && instance?.GenericType != owner)
            return null;

        var getter = owner.Properties.SingleOrDefault(p => p.Name == propertyName)?.Getter;
        if (getter is not { IsStatic: false, Parameters.Count: 0, GenericParameters.Count: 0 }
            || getter.Visibility != MethodAttributes.Public || getter.ReturnType != definition.FieldType
            || getter.GetExtraData<MethodDefinition>("AsmResolverMethod") == caller)
            return null;

        return instance == null ? getter : new ConcreteGenericMethodAnalysisContext(getter, instance.GenericArguments, []);
    }
}
