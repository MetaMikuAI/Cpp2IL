using System;
using Cpp2IL.Core.Analysis;

namespace Cpp2IL.Core.Tests.Analysis;

public class ClassEnsureCallRecoveryTests
{
    // il2cpp helpers from an ARM64 build that make sure a class / method is initialized and return it.
    private const string InitClass = "fe4fbfa9f30300aaf2ca009460da40b980000035e00313aafe4fc1a8c0035fd659ae0094e1031faa2e9a0194fe4fbfa9f30300aa61000036f2ffff9705000014e4ca009468da40b91f01007173029f9ae00313aafe4fc1a8c0035fd6fe4fbfa9f30300aad2110194e00313aafe4fc1a8c0035fd6fe0f1cf8f85f01a9f65702a9";
    private const string InitMethod = "fe4fbfa9f30300aad2110194e00313aafe4fc1a8c0035fd6fe0f1cf8f85f01a9f65702a9f44f03a9283040f9680200b4085c4279f40300aa08020034f303022af50301aaf6031faaf7031faa985a40f9e00315aae20314aa016b76f81300009480010037885e4279f7060091d6420091ff0208ebc3feff54e0031faaf44f43a9";

    // The object compare-exchange also ends in mov x0, x19, but x19 holds the value it loaded, not X0.
    private const string CompareExchange = "fe4fbfa908fc5fc81f0102eba100005401fc09c889ffff3529008052030000145f3f03d5e9031f2abf3b03d53f0100715310889a9b93fe97e00313aafe4fc1a8c0035fd6";

    [TestCase(InitClass, 0x48DF244UL, true)]
    [TestCase(InitMethod, 0x48DF2A0UL, true)]
    [TestCase(CompareExchange, 0x49654E4UL, false)]
    public void RecognisesHelpersReturningTheirArgument(string hex, ulong address, bool expected)
        => Assert.That(ClassEnsureCallRecovery.ReturnsFirstArgument(Convert.FromHexString(hex), address), Is.EqualTo(expected));
}
