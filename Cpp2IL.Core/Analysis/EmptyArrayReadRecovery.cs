using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

public static class EmptyArrayReadRecovery
{
    public static MethodAnalysisContext? TryGetFactory(FieldAnalysisContext field, MethodDefinition caller)
    {
        if (field is not ConcreteGenericFieldAnalysisContext concrete
            || concrete.DeclaringType is not GenericInstanceTypeAnalysisContext { GenericArguments.Count: 1 } instance)
            return null;

        var definition = concrete.BaseFieldContext;
        var owner = definition.DeclaringType;
        if (owner.FullName != "System.EmptyArray`1" || owner.GenericParameters.Count != 1 || instance.GenericType != owner
            || owner.DeclaringAssembly.Name != "mscorlib"
            || owner.DeclaringAssembly != owner.AppContext.SystemTypes.SystemObjectType.DeclaringAssembly
            || definition.Name != "Value" || !definition.IsStatic
            || (definition.Attributes & FieldAttributes.FieldAccessMask) != FieldAttributes.Public
            || (definition.Attributes & FieldAttributes.InitOnly) == 0
            || definition.FieldType is not SzArrayTypeAnalysisContext { ElementType: GenericParameterTypeAnalysisContext parameter }
            || parameter.Owner != owner || parameter.Index != 0
            || concrete.FieldType is not SzArrayTypeAnalysisContext valueType || valueType.ElementType != instance.GenericArguments[0])
            return null;

        var factory = owner.DeclaringAssembly.GetTypeByFullName("System.Array")?.Methods.SingleOrDefault(m =>
            m.Name == "Empty" && m.IsStatic && m.Visibility == MethodAttributes.Public
            && m.Parameters.Count == 0 && m.GenericParameters.Count == 1);
        if (factory == null || factory.GetExtraData<MethodDefinition>("AsmResolverMethod") == caller
            || factory.ReturnType is not SzArrayTypeAnalysisContext { ElementType: GenericParameterTypeAnalysisContext result }
            || result.Owner != factory || result.Index != 0)
            return null;

        // Array.Empty<T> returns this exact shared field in the Mono runtime.
        return new ConcreteGenericMethodAnalysisContext(factory, [], instance.GenericArguments);
    }
}
