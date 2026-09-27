using System;
using Cpp2IL.Core.Analysis;

namespace Cpp2IL.Core.Tests.Analysis;

public class SharedFieldAccessRecoveryTests
{
    // il2cpp_codegen_get_instance_field_data_pointer of an ARM64 build: obj + field->offset, less the object
    // header when the field's parent is a value type.
    private const string InstanceFieldAddress = "280840f9291880b9082940b90900098b2a4100d11f01007120a18a9ac0035fd6";
    // The static counterpart adds the offset to the parent's static_fields instead.
    private const string StaticFieldAddress = "080840f9091880b9085d40f90001098bc0035fd6";

    [TestCase(InstanceFieldAddress, 0x4905940UL, true)]
    [TestCase(StaticFieldAddress, 0x4909224UL, false)]
    public void RecognisesInstanceFieldAddressHelper(string hex, ulong address, bool expected)
        => Assert.That(SharedFieldAccessRecovery.IsAddressHelper(Convert.FromHexString(hex), address), Is.EqualTo(expected));
}
