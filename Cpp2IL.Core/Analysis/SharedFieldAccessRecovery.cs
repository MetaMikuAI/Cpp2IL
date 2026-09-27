using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Fully shared generic code cannot know its own field offsets, so it reaches an instance field through the
/// field's FieldInfo, the entry of its class's <c>fields</c> array (<c>klass->fields + index * sizeof(FieldInfo)</c>):
/// <list type="bullet">
/// <item>address helper (obj, field) => <c>&amp;obj.field</c> (il2cpp_codegen_get_instance_field_data_pointer:
/// <c>obj + field->offset</c>, less the object header for a value type's field)</item>
/// <item>store helper (obj, field, value): the address helper, then a store of the value there => <c>obj.field = value</c></item>
/// </list>
/// Loads and stores through a recovered address become accesses of the field itself.
/// </summary>
public static class SharedFieldAccessRecovery
{
    internal enum HelperKind
    {
        None,
        Address,
        Store,
    }

    private static readonly ConcurrentDictionary<(ApplicationAnalysisContext App, ulong Target), HelperKind> Helpers = new();

    // Il2CppClass::fields and sizeof(FieldInfo) in the 64-bit layout (name, type, parent, offset, token).
    private const int FieldsOffset = 0x80;
    private const int FieldInfoSize = 0x20;
    // FieldInfo::parent and FieldInfo::offset
    private const int ParentOffset = 0x10;
    private const int OffsetOffset = 0x18;

    private const int ScanBytes = 24 * 4;

    public static bool Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet
            || method.AppContext.Binary.PointerSizeBytes != 8 || method.AppContext.MetadataVersion is < 29 or >= 32
            || method.ControlFlowGraph is not { } graph)
            return false;

        var instructions = graph.Instructions;
        var definitions = instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!).Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());

        var uses = instructions.SelectMany(DeadCodeEliminator.UsedLocals).ToHashSet();
        var addresses = new Dictionary<LocalVariable, FieldReference>();
        var changed = false;
        foreach (var instruction in instructions)
        {
            // An unknown target is taken to return a value; a store helper's result is never used.
            var first = instruction.OpCode == OpCode.Call ? 2 : 1;
            if (!instruction.IsCall || instruction.Operands.Count < first + 2 || instruction.Operands[0] is not Immediate target
                || instruction.Operands[first] is not LocalVariable obj || instruction.Operands[first + 1] is not LocalVariable info
                || Field(info, obj, definitions) is not { } field)
                continue;

            var kind = Kind(method.AppContext, target.UnsignedValue);
            if (kind == HelperKind.Address && instruction.OpCode == OpCode.Call && instruction.Operands[1] is LocalVariable result)
            {
                var reference = new FieldReference(field, obj, field.Offset);
                addresses[result] = reference;
                instruction.OpCode = OpCode.Move;
                instruction.SetOperands(result, new AddressOf(reference));
                changed = true;
            }
            else if (kind == HelperKind.Store && instruction.Operands.Count > first + 2 && field.FieldType is not GenericParameterTypeAnalysisContext
                     && (first == 1 || instruction.Operands[1] is not LocalVariable unused || !uses.Contains(unused)))
            {
                var value = instruction.Operands[first + 2];
                instruction.OpCode = OpCode.Move;
                instruction.SetOperands(new FieldReference(field, obj, field.Offset), value);
                changed = true;
            }
        }

        if (!changed)
            return false;

        // A load or store through a recovered address is an access of the field. A value of a type argument
        // is copied by size rather than loaded, so its address is left alone.
        if (addresses.Count != 0)
            foreach (var instruction in instructions)
                for (var i = 0; i < instruction.Operands.Count; i++)
                    if (instruction.Operands[i] is MemoryOperand { Base: LocalVariable pointer, Index: null, Addend: 0 } memory
                        && addresses.TryGetValue(pointer, out var reference) && reference.Field.FieldType is not GenericParameterTypeAnalysisContext)
                        instruction.SetOperand(i, new FieldReference(reference.Field, reference.Local, reference.Offset) { AccessSize = memory.AccessSize });

        DeadCodeEliminator.Run(graph);
        return true;
    }

    // The field whose FieldInfo the operand holds: klass->fields of the class obj is an instance of, plus index * sizeof(FieldInfo).
    private static FieldAnalysisContext? Field(LocalVariable info, LocalVariable obj, Dictionary<LocalVariable, Instruction> definitions)
    {
        long delta = 0;
        var fields = info;
        if (definitions.TryGetValue(info, out var definition) && definition is { OpCode: OpCode.Add, Operands: [_, var left, var right] })
        {
            if (left is Immediate) (left, right) = (right, left);
            if (left is not LocalVariable table || right is not Immediate { Value: >= 0 } offset)
                return null;
            fields = table;
            delta = offset.Value;
        }

        if (delta % FieldInfoSize != 0
            || !definitions.TryGetValue(fields, out var load)
            || load is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: LocalVariable klassLocal, Index: null, Addend: FieldsOffset }] })
            return null;

        // The class comes from the RGCTX, or is read from the object's header (obj->klass).
        var ownerType = klassLocal.Type switch
        {
            RuntimeClassTypeAnalysisContext klass => klass.RepresentedType,
            _ when definitions.TryGetValue(klassLocal, out var header)
                   && header is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: LocalVariable headerOf, Index: null, Addend: 0 }] }
                   && headerOf == obj && obj.Type is { IsValueType: false } objectType and not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext)
                => objectType,
            _ => null,
        };
        if (ownerType == null)
            return null;

        var owner = ownerType is GenericInstanceTypeAnalysisContext instance ? instance.GenericType : ownerType;
        var index = (int)(delta / FieldInfoSize);
        if (index >= owner.Fields.Count || owner.Fields[index] is not { IsStatic: false } field)
            return null;
        if (ownerType is GenericInstanceTypeAnalysisContext generic)
            field = new ConcreteGenericFieldAnalysisContext(field, generic);

        // The object must be one of the class: an address in some other object is not this field.
        var objType = obj.Type is GenericInstanceTypeAnalysisContext objInstance ? objInstance.GenericType : obj.Type;
        if (objType is ByRefTypeAnalysisContext byRef)
            objType = byRef.ElementType is GenericInstanceTypeAnalysisContext element ? element.GenericType : byRef.ElementType;
        // An interface or object typed receiver (a value returned as IEnumerator) does not rule it out.
        return objType == null || objType == owner || objType.IsInterface || objType.FullName == "System.Object" ? field : null;
    }

    private static HelperKind Kind(ApplicationAnalysisContext app, ulong target) => Helpers.GetOrAdd((app, target), key => Classify(key.App, key.Target, 0));

    private static HelperKind Classify(ApplicationAnalysisContext app, ulong target, int depth)
    {
        if (depth > 3 || app.MethodsByAddress.ContainsKey(target) || Disassemble(app, target) is not { } code)
            return HelperKind.None;

        // A thunk: an unconditional branch to the helper itself.
        if (code[0] is { Mnemonic: Arm64Mnemonic.B, MnemonicConditionCode: Arm64ConditionCode.NONE or Arm64ConditionCode.AL })
            return Classify(app, code[0].BranchTarget, depth + 1);

        if (IsAddressHelper(code))
            return HelperKind.Address;

        // A store helper saves the value (X2/W2), calls the address helper and stores the value at the address it returns.
        var call = code.FindIndex(i => i.Mnemonic == Arm64Mnemonic.BL && Classify(app, i.BranchTarget, depth + 1) == HelperKind.Address);
        if (call < 0 || call + 1 >= code.Count
            || code[call + 1] is not { Mnemonic: Arm64Mnemonic.STR or Arm64Mnemonic.STRB or Arm64Mnemonic.STRH, MemBase: Arm64Register.X0, MemOffset: 0 } store
            || code.Take(call).Any(i => i.Mnemonic is Arm64Mnemonic.B or Arm64Mnemonic.RET))
            return HelperKind.None;
        var saved = code.FindLastIndex(call, i => i.Mnemonic == Arm64Mnemonic.MOV && SameRegister(i.Op0Reg, store.Op0Reg));
        return saved >= 0 && SameRegister(code[saved].Op1Reg, Arm64Register.X2) ? HelperKind.Store : HelperKind.None;
    }

    /// <summary>
    /// <c>ldr xA, [x1, #parent]; ldrsw xB, [x1, #offset]; ... add xC, x0, xB ... ret</c>: obj + field->offset.
    /// </summary>
    internal static bool IsAddressHelper(ReadOnlySpan<byte> bytes, ulong address)
    {
        List<Arm64Instruction> code = Disassembler.Disassemble(bytes, address, new Disassembler.Options(true, true, false)).ToList();
        return IsAddressHelper(code);
    }

    private static bool IsAddressHelper(IReadOnlyList<Arm64Instruction> code)
    {
        var ret = code.ToList().FindIndex(i => i.Mnemonic == Arm64Mnemonic.RET);
        if (ret < 2
            || code[0] is not { Mnemonic: Arm64Mnemonic.LDR, MemBase: Arm64Register.X1, MemOffset: ParentOffset }
            || code[1] is not { Mnemonic: Arm64Mnemonic.LDRSW, MemBase: Arm64Register.X1, MemOffset: OffsetOffset } offset)
            return false;
        return code.Take(ret).Any(i => i.Mnemonic == Arm64Mnemonic.ADD && i.Op1Reg == Arm64Register.X0 && i.Op2Reg == offset.Op0Reg)
            && code.Take(ret).All(i => i.Mnemonic is not (Arm64Mnemonic.BL or Arm64Mnemonic.B or Arm64Mnemonic.STR or Arm64Mnemonic.STP));
    }

    private static bool SameRegister(Arm64Register a, Arm64Register b) => Number(a) is { } x && x == Number(b);

    private static int? Number(Arm64Register register) => register switch
    {
        >= Arm64Register.X0 and <= Arm64Register.X30 => register - Arm64Register.X0,
        >= Arm64Register.W0 and <= Arm64Register.W30 => register - Arm64Register.W0,
        _ => null,
    };

    private static List<Arm64Instruction>? Disassemble(ApplicationAnalysisContext app, ulong target)
    {
        var binary = app.Binary;
        if (!binary.TryMapVirtualAddressToRaw(target, out var raw) || raw < 0 || raw > binary.RawLength - ScanBytes)
            return null;
        try
        {
            ReadOnlySpan<byte> bytes = binary.GetRawBinaryContent().Slice((int)raw, ScanBytes);
            List<Arm64Instruction> code = Disassembler.Disassemble(bytes, target, new Disassembler.Options(true, true, false)).ToList();
            return code.Count == 0 ? null : code;
        }
        catch
        {
            return null;
        }
    }
}
