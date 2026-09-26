using System;
using Cpp2IL.Core.Analysis;

namespace Cpp2IL.Core.Tests.Analysis;

public class SharedValueStorageRecoveryTests
{
    // The fully shared generic helpers of an ARM64 build: unbox into a buffer (obj, class, buffer) tests the
    // class in X1 for a value type, the constrained-call helper (class, method, ...) tests it in X0.
    private const string UnboxInto = "fe57bea9f44f01a9282840b9f50302aaf30301aaf40300aae800f837940200b4e00314aae10313aa";
    private const string ConstrainedInvoke = "fe5fbda9f65701a9f44f02a9082840b9f30305aaf40304aaf60303aaf50301aa4801f837d60240f9";
    private const string CompareExchange = "fe4fbfa908fc5fc81f0102eba100005401fc09c889ffff3529008052030000145f3f03d5e9031f2abf3b";

    [TestCase(UnboxInto, 0x4909354UL, "UnboxInto")]
    [TestCase(ConstrainedInvoke, 0x4909D44UL, "ConstrainedInvoke")]
    [TestCase(CompareExchange, 0x49654E4UL, "None")]
    public void ClassifiesSharedValueHelpers(string hex, ulong address, string expected)
        => Assert.That(SharedValueStorageRecovery.Classify(Convert.FromHexString(hex), address).ToString(), Is.EqualTo(expected));
}
