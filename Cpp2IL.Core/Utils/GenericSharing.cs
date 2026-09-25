using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils;

/// <summary>
/// IL2CPP compiles one body for all instantiations that share a representation. A reference-type
/// argument shares the <c>System.Object</c> body, an enum argument shares the body of the internal
/// corlib enum with the same underlying type (<c>System.Int32Enum</c> for an int-backed enum), and a
/// value-type generic instance shares the body of the same instance over the shared forms of its
/// arguments. A call into such a body names the shared instantiation, so specializing it to the
/// instantiation the caller meant needs the relation between a shared argument and a concrete one.
/// </summary>
internal static class GenericSharing
{
    /// <summary>
    /// Whether <paramref name="type"/> is an argument IL2CPP compiles shared code for: <c>System.Object</c>,
    /// a corlib enum, or a value-type instance over either.
    /// </summary>
    public static bool IsSharedRepresentative(TypeAnalysisContext type) => type switch
    {
        GenericInstanceTypeAnalysisContext { IsValueType: true } instance => instance.GenericArguments.Any(IsSharedRepresentative),
        _ => type == type.AppContext.SystemTypes.SystemObjectType || IsSharedEnum(type),
    };

    /// <summary>
    /// Whether the body compiled for the argument <paramref name="shared"/> also serves the argument
    /// <paramref name="concrete"/>. A type is its own shared form unless it is a reference type, an
    /// enum or a value-type generic instance. A generic parameter of the calling code stands for
    /// whatever that code's own instantiation binds it to, so only its constraints can rule a body out.
    /// </summary>
    public static bool IsSharedFormOf(TypeAnalysisContext shared, TypeAnalysisContext concrete)
    {
        if (ReferenceEquals(shared, concrete))
            return true;

        if (concrete is GenericParameterTypeAnalysisContext parameter)
            return !parameter.Attributes.HasFlag(shared.IsValueType
                ? GenericParameterAttributes.ReferenceTypeConstraint
                : GenericParameterAttributes.NotNullableValueTypeConstraint);

        if (shared == shared.AppContext.SystemTypes.SystemObjectType)
            return !concrete.IsValueType;

        if (IsSharedEnum(shared))
            return concrete.IsEnumType && concrete.EnumUnderlyingType is { } underlying && ReferenceEquals(underlying, shared.EnumUnderlyingType);

        return shared is GenericInstanceTypeAnalysisContext { IsValueType: true } sharedInstance
               && concrete is GenericInstanceTypeAnalysisContext concreteInstance
               && ReferenceEquals(sharedInstance.GenericType, concreteInstance.GenericType)
               && AreSharedFormsOf(sharedInstance.GenericArguments, concreteInstance.GenericArguments);
    }

    private static bool AreSharedFormsOf(IReadOnlyList<TypeAnalysisContext> shared, IReadOnlyList<TypeAnalysisContext> concrete)
        => shared.Count == concrete.Count && shared.Zip(concrete).All(pair => IsSharedFormOf(pair.First, pair.Second));

    /// <summary>
    /// Whether the method metadata registers at a call address, <paramref name="registered"/>, may
    /// share its body with <paramref name="called"/>. An address can serve more instantiations than
    /// metadata registers there: full generic sharing compiles one body for all of them and identical
    /// code folding merges equal bodies, so an object or value-type argument proves nothing. An enum
    /// argument does: IL2CPP compiles a separate body per underlying type, which serves only enums of
    /// that type (or a generic parameter of calling code that such an enum instantiates).
    /// </summary>
    public static bool MayServe(MethodAnalysisContext registered, MethodAnalysisContext called)
    {
        if (registered.DeclaringType is GenericInstanceTypeAnalysisContext registeredType
            && called.DeclaringType is GenericInstanceTypeAnalysisContext calledType
            && !MayServe(registeredType.GenericArguments, calledType.GenericArguments))
            return false;

        // A partial instantiation names no method arguments, so it pins nothing either.
        return registered is not ConcreteGenericMethodAnalysisContext { MethodGenericParameters: { Count: > 0 } registeredArguments }
               || called is not ConcreteGenericMethodAnalysisContext { MethodGenericParameters: { Count: > 0 } calledArguments }
               || MayServe(registeredArguments, calledArguments);
    }

    /// <inheritdoc cref="MayServe(MethodAnalysisContext, MethodAnalysisContext)"/>
    public static bool MayServe(IReadOnlyList<TypeAnalysisContext> registered, IReadOnlyList<TypeAnalysisContext> called)
        => registered.Count == called.Count && registered.Zip(called).All(pair => MayServe(pair.First, pair.Second));

    private static bool MayServe(TypeAnalysisContext registered, TypeAnalysisContext called)
    {
        if (IsSharedEnum(registered))
            return IsSharedFormOf(registered, called);

        return registered is not GenericInstanceTypeAnalysisContext { IsValueType: true } registeredInstance
               || called is not GenericInstanceTypeAnalysisContext calledInstance
               || !ReferenceEquals(registeredInstance.GenericType, calledInstance.GenericType)
               || MayServe(registeredInstance.GenericArguments, calledInstance.GenericArguments);
    }

    // The corlib declares one internal enum per integral underlying type, named after it
    // (System.SByteEnum ... System.UInt64Enum), purely as the argument of shared enum code.
    private static bool IsSharedEnum(TypeAnalysisContext type)
        => type is { IsEnumType: true, Namespace: "System", EnumUnderlyingType: { Namespace: "System" } underlying }
           && (type.Attributes & TypeAttributes.VisibilityMask) == TypeAttributes.NotPublic
           && type.DeclaringAssembly == type.AppContext.SystemTypes.SystemObjectType.DeclaringAssembly
           && type.Name == underlying.Name + "Enum";
}
