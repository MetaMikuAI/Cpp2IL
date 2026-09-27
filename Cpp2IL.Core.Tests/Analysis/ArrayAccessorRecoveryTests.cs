using System;
using Cpp2IL.Core.Analysis;

namespace Cpp2IL.Core.Tests.Analysis;

public class ArrayAccessorRecoveryTests
{
    // Bounds-checked element accessors of an ARM64 build: an object array store (index scaled by 8, then the
    // write barrier) and a byte array load.
    private const string ReferenceSet = "fe0f1ff8081840b93f00086bc2000054000c018b020c02f8e10302aafe0741f8a6991614619a1694fe0f1ff8081840b9";
    private const string ByteGet = "fe0f1ff8081840b93f00086ba20000540800018b00814039fe0741f8c0035fd6589a169400400091b8f21f1400600091";
    // A static field address helper is no element accessor.
    private const string StaticFieldAddress = "080840f9091880b9085d40f90001098bc0035fd6fe4fbfa9080840f9091880b9e203022a085d40f91301098be00313aa";

    [TestCase(ReferenceSet, 0x4362AC0UL, "Set", 8)]
    [TestCase(ByteGet, 0x4362AE8UL, "Get", 1)]
    [TestCase(StaticFieldAddress, 0x4909224UL, "None", 0)]
    public void ClassifiesElementAccessors(string hex, ulong address, string kind, int size)
    {
        var (actualKind, actualSize) = ArrayAccessorRecovery.Classify(Convert.FromHexString(hex), address);
        Assert.That((actualKind.ToString(), actualSize), Is.EqualTo((kind, size)));
    }
}
