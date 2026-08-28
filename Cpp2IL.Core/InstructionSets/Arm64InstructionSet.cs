using System.Collections.Generic;
using System.Linq;
using System.Text;
using Cpp2IL.Core.Api;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using Gee.External.Capstone.Arm64;

namespace Cpp2IL.Core.InstructionSets;

public class Arm64InstructionSet : Cpp2IlInstructionSet
{
    public override BinarySlice GetRawBytesForMethod(MethodAnalysisContext context, bool isAttributeGenerator)
    {
        var binary = context.AppContext.Binary;

        //Avoid use of capstone where possible
        if (true || context is not ConcreteGenericMethodAnalysisContext)
        {
            //Managed method or attr gen => grab raw byte range between a and b
            var startOfNextFunction = (int)MiscUtils.GetAddressOfNextFunctionStart(context.UnderlyingPointer, binary) - 1;
            var ptrAsInt = (int)context.UnderlyingPointer;
            var count = startOfNextFunction - ptrAsInt;

            if (startOfNextFunction > 0)
                return new BinarySlice(binary, ptrAsInt, count);
        }

        var instructions = Arm64Utils.GetArm64MethodBodyAtVirtualAddress(binary, context.UnderlyingPointer);

        return new BinarySlice(instructions.SelectMany(i => i.Bytes).ToArray());
    }

    public override List<Instruction> GetIsilFromMethod(MethodAnalysisContext context)
    {
        return [];
    }

    public override List<IOperand> GetParameterOperandsFromMethod(MethodAnalysisContext context)
    {
        return [];
    }

    public override ulong GetInternalCallTarget(MethodAnalysisContext method)
    {
        var start = GetPointerForMethod(method);
        var length = method.RawBytes.Length;

        if (start == 0 || length < 4)
            return 0;

        List<Arm64Instruction> instructions;
        try
        {
            instructions = Arm64Utils.GetArm64MethodBodyAtVirtualAddress(method.AppContext.Binary, start);
        }
        catch
        {
            return 0;
        }

        var end = start + (ulong)length;
        var target = 0ul;

        foreach (var instruction in instructions)
        {
            if (instruction.Mnemonic != "b" || !instruction.Details.Operands.Any())
                continue;

            var branch = (ulong)instruction.Details.Operands[0].Immediate;
            if (branch >= start && branch < end)
                continue;

            if (target != 0 && target != branch)
                return 0;

            target = branch;
        }

        return target;
    }

    public override BaseKeyFunctionAddresses CreateKeyFunctionAddressesInstance() => new Arm64KeyFunctionAddresses();

    public override string PrintAssembly(MethodAnalysisContext context)
    {
        var sb = new StringBuilder();

        var instructions = Arm64Utils.GetArm64MethodBodyAtVirtualAddress(context.AppContext.Binary, context.UnderlyingPointer);

        var first = true;
        foreach (var instruction in instructions)
        {
            if (!first)
                sb.AppendLine();

            first = false;
            sb.Append("0x").Append(instruction.Address.ToString("X")).Append(" ").Append(instruction.Mnemonic).Append(" ").Append(instruction.Operand);
        }

        return sb.ToString();
    }
}
