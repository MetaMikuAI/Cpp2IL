using System.Buffers.Binary;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

public static class ThreadStaticFieldRecovery
{
    public static bool TryTypeLookup(Instruction instruction, MethodAnalysisContext method,
        Dictionary<LocalVariable, Instruction> definitions)
    {
        if (instruction is not { OpCode: OpCode.Call, Operands: [Immediate address, LocalVariable result, var klass, ..] })
            return false;
        var seen = new HashSet<LocalVariable>();
        while (klass is LocalVariable local && seen.Add(local) && definitions.TryGetValue(local, out var definition)
            && definition is { OpCode: OpCode.Move or OpCode.Phi, Operands: [_, var source] })
            klass = source;
        var owner = klass is RuntimeClassTypeAnalysisContext runtimeClass ? runtimeClass.RepresentedType : klass as TypeAnalysisContext;
        if (owner == null || !owner.Fields.Any(f => f.IsStatic && f.Offset < -1 && (f.Attributes & FieldAttributes.Literal) == 0)
            || !IsLookup(method.AppContext, address.UnsignedValue))
            return false;

        result.Type = new StaticFieldStorageTypeAnalysisContext(owner, owner.DeclaringAssembly, isThreadStatic: true);
        // The wrapper takes only Il2CppClass*. Guessed argument registers otherwise
        // keep unrelated definitions alive and can poison their inferred types.
        instruction.SetOperands(address, result, instruction.Operands[2]);
        return true;
    }

    internal static bool IsLookup(ApplicationAnalysisContext app, ulong address)
    {
        // This class layout is shared by metadata v29/v31. Other layouts and
        // architectures need their own recognizer; do not guess from call usage.
        if (app.InstructionSet is not NewArmV8InstructionSet || app.Binary.is32Bit || app.Binary.IsBigEndian
            || app.MetadataVersion is < 29 or >= 32
            || !app.Binary.TryMapVirtualAddressToRaw(address, out var raw))
            return false;
        var bytes = app.Binary.GetRawBinaryContent();
        if (raw < 0 || raw > bytes.Length - 8)
            return false;
        return IsLookupThunk(BinaryPrimitives.ReadUInt32LittleEndian(bytes.Slice((int)raw, 4)),
            BinaryPrimitives.ReadUInt32LittleEndian(bytes.Slice((int)raw + 4, 4)), address);
    }

    internal static bool IsLookupThunk(uint load, uint branch, ulong address)
    {
        // LDR W0, [X0, #0x114] (Il2CppClass::thread_static_fields_offset), then B.
        var target = NewArm64KeyFunctionAddresses.DecodeBranchThunk(branch, address + 4);
        return load == 0xB9411400 && target != 0 && target != address && target != address + 4;
    }
}
