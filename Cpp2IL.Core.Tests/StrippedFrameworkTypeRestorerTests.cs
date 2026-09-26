using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests;

public class StrippedFrameworkTypeRestorerTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [TestCase("System", "ValueType", TypeAttributes.AutoLayout, true)] // e.g. a compiler-generated state machine
    [TestCase("System", "ValueType", TypeAttributes.SequentialLayout, false)]
    [TestCase("System", "ValueType", TypeAttributes.ExplicitLayout, true)]
    [TestCase("System", "Object", TypeAttributes.AutoLayout, false)]
    [TestCase("System", "Object", TypeAttributes.SequentialLayout, true)]
    [TestCase("System", "Enum", TypeAttributes.AutoLayout, false)]
    public void LayoutNeedsAnAttributeOnlyWhenItDiffersFromTheCSharpDefault(string ns, string baseName, TypeAttributes layout, bool expected)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var corlib = app.SystemTypes.SystemObjectType.DeclaringAssembly;
        var type = corlib.InjectType("Tests", "Layout", corlib.GetTypeByFullName($"{ns}.{baseName}"), TypeAttributes.Public | layout);
        Assert.That(StrippedFrameworkTypeRestorer.HasNonDefaultLayout(type), Is.EqualTo(expected));
    }

    [TestCase(MethodImplAttributes.AggressiveInlining, true)]
    [TestCase(MethodImplAttributes.InternalCall, true)]
    [TestCase(MethodImplAttributes.PreserveSig, false)]
    [TestCase(MethodImplAttributes.Runtime, false)]
    [TestCase(MethodImplAttributes.Managed, false)]
    public void OnlyImplementationOptionsNeedMethodImpl(MethodImplAttributes attributes, bool expected)
        => Assert.That(StrippedFrameworkTypeRestorer.HasMethodImplOptions(attributes), Is.EqualTo(expected));

    [TestCase("System.Runtime.InteropServices", "StructLayoutAttribute", "LayoutKind", "Sequential=0,Explicit=2,Auto=3")]
    [TestCase("System.Runtime.CompilerServices", "MethodImplAttribute", "MethodImplOptions",
        "Unmanaged=4,NoInlining=8,ForwardRef=16,Synchronized=32,NoOptimization=64,PreserveSig=128,AggressiveInlining=256,InternalCall=4096")]
    public void RestoresAStrippedPseudoAttributeWithItsFrameworkShape(string ns, string attributeName, string enumName, string members)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var corlib = app.SystemTypes.SystemObjectType.DeclaringAssembly;
        var original = corlib.GetTypeByFullName($"{ns}.{attributeName}");

        StrippedFrameworkTypeRestorer.Restore(app);
        StrippedFrameworkTypeRestorer.Restore(app);

        Assert.That(corlib.Types.Count(t => t.FullName == $"{ns}.{attributeName}"), Is.LessThanOrEqualTo(1));
        var restored = corlib.GetTypeByFullName($"{ns}.{attributeName}");
        if (original != null)
        {
            Assert.That(restored, Is.SameAs(original), "a type the metadata kept is never replaced");
            return;
        }
        if (restored == null)
            Assert.Ignore("the test game's metadata has no flags that need this attribute");

        var enumType = corlib.GetTypeByFullName($"{ns}.{enumName}")!;
        Assert.That(enumType.IsEnumType, Is.True);
        var literals = enumType.Fields.Where(f => f.IsStatic).Select(f => $"{f.Name}={f.ConstantValue}");
        Assert.That(string.Join(",", literals), Is.EqualTo(members));
        Assert.That(restored!.BaseType, Is.SameAs(app.SystemTypes.SystemAttributeType));
        Assert.That(restored.Methods.Any(m => m.Name == ".ctor" && m.Parameters is [{ ParameterType: var p }] && p == enumType), Is.True);
        Assert.That(restored.Properties.Single(p => p.Name == "Value").PropertyType, Is.SameAs(enumType));
    }

    [Test]
    public void RestoresAssemblyVersionAttribute()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        StrippedFrameworkTypeRestorer.Restore(app);
        var attribute = app.SystemTypes.SystemObjectType.DeclaringAssembly.GetTypeByFullName("System.Reflection.AssemblyVersionAttribute");
        Assert.That(attribute, Is.Not.Null);
        Assert.That(attribute!.Methods.Any(m => m.Name == ".ctor" && m.Parameters is [{ ParameterType: var p }] && p == app.SystemTypes.SystemStringType));
    }

    [Test]
    public void RestoresTheMathConstantsADecompilerWritesForLiterals()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var math = app.SystemTypes.SystemObjectType.DeclaringAssembly.GetTypeByFullName("System.Math")!;
        var kept = math.Fields.Where(f => f.Name is "PI" or "E").ToList();

        StrippedFrameworkTypeRestorer.Restore(app);
        StrippedFrameworkTypeRestorer.Restore(app);

        foreach (var (name, value) in new[] { ("PI", System.Math.PI), ("E", System.Math.E) })
        {
            var field = math.Fields.Single(f => f.Name == name);
            if (kept.Contains(field))
                continue; // a constant the metadata kept is never replaced
            Assert.That(field.IsStatic && field.Attributes.HasFlag(FieldAttributes.Literal) && field.Attributes.HasFlag(FieldAttributes.Public));
            Assert.That(field.FieldType, Is.SameAs(app.SystemTypes.SystemDoubleType));
            Assert.That(field.ConstantValue, Is.EqualTo(value));
        }
    }

    [TestCase(true)]
    [TestCase(false)]
    public void RestoresTheGetterOfAWriteOnlyAutoProperty(bool autoProperty)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var corlib = app.SystemTypes.SystemObjectType.DeclaringAssembly;
        var type = corlib.InjectType("Tests", "MenuAttribute", app.SystemTypes.SystemAttributeType, TypeAttributes.Public | TypeAttributes.Sealed);
        type.InjectFieldContext(autoProperty ? "<menuName>k__BackingField" : "_menuName", app.SystemTypes.SystemStringType, FieldAttributes.Private);
        var setter = type.InjectMethodContext("set_menuName", app.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.HideBySig | MethodAttributes.SpecialName, app.SystemTypes.SystemStringType);
        var property = type.InjectPropertyContext("menuName", app.SystemTypes.SystemStringType, null, setter, PropertyAttributes.None);

        StrippedFrameworkTypeRestorer.RestoreAutoPropertyGetters(type);

        if (!autoProperty)
        {
            Assert.That(property.Getter, Is.Null, "without an auto-property backing field the getter body is unknown");
            return;
        }
        Assert.That(property.Getter, Is.Not.Null);
        Assert.That(property.Getter!.Name, Is.EqualTo("get_menuName"));
        Assert.That(property.Getter.ReturnType, Is.SameAs(app.SystemTypes.SystemStringType));
        Assert.That(property.Getter.Parameters, Is.Empty);
        Assert.That(type.Methods, Does.Contain(property.Getter));
    }
}
