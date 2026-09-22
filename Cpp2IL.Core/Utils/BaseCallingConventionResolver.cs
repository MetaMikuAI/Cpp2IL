using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils;

public abstract class BaseCallingConventionResolver
{
    public static bool IsFloatingPoint(TypeAnalysisContext type)
        => type == type.AppContext.SystemTypes.SystemSingleType || type == type.AppContext.SystemTypes.SystemDoubleType;

    protected static bool IsFloatingPoint(ParameterAnalysisContext par) => IsFloatingPoint(par.ParameterType);

    public abstract Register ReturnRegister(MethodAnalysisContext ctx);

    public abstract bool ReturnsViaHiddenBuffer(MethodAnalysisContext ctx);

    public abstract Register? HiddenReturnBufferRegister(MethodAnalysisContext ctx);

    public abstract IOperand[] ResolveForManaged(MethodAnalysisContext ctx);

    protected abstract (string[] Integer, string[] Float) RawRegisters(ApplicationAnalysisContext app);

    // MSVC style: argument slot n is integer register n or float register n, not both
    protected virtual bool UsesShadowedArgumentSlots(ApplicationAnalysisContext app) => false;

    // false when the return buffer pointer lives outside the argument registers (e.g. arm64 uses x8)
    protected virtual bool HiddenBufferConsumesArgumentSlot => true;

    protected virtual int IntegerArgumentSlots(ParameterAnalysisContext parameter) => 1;

    public IOperand[] ResolveForUnmanaged(ApplicationAnalysisContext app, ulong target)
    {
        var (integerRegisters, floatRegisters) = RawRegisters(app);
        // A proven ELF import has a native signature and no hidden MethodInfo or FP args.
        if (this is Arm64CallingConventionResolver
            && Arm64ImportResolver.IntegerArgumentCount(Arm64ImportResolver.Resolve(app.Binary, target)) is { } count)
            return integerRegisters.Take(count).Select(name => (IOperand)new Register(null, name)).ToArray();

        // Unknown signatures still preserve every argument register.
        return integerRegisters.Concat(floatRegisters).Select(name => (IOperand)new Register(null, name)).ToArray();
    }

    public bool HasRawArgumentLayout(Instruction call, ApplicationAnalysisContext app)
    {
        var (integerRegisters, floatRegisters) = RawRegisters(app);
        var argBase = ArgBase(call);

        if (call.Operands.Count != argBase + integerRegisters.Length + floatRegisters.Length)
            return false;

        for (var i = 0; i < integerRegisters.Length; i++)
            if (RegisterName(call.Operands[argBase + i]) != integerRegisters[i])
                return false;

        for (var i = 0; i < floatRegisters.Length; i++)
            if (RegisterName(call.Operands[argBase + integerRegisters.Length + i]) != floatRegisters[i])
                return false;

        return true;
    }

    // TODO Fix handling of params on the stack here
    public void RemapRawArguments(Instruction call, MethodAnalysisContext resolved)
    {
        var app = resolved.AppContext;

        if (!HasRawArgumentLayout(call, app))
            return;

        var (integerRegisters, floatRegisters) = RawRegisters(app);
        var argBase = ArgBase(call);

        var slots = new List<(bool IsFloat, bool Emit, int Count)>();
        if (ReturnsViaHiddenBuffer(resolved) && HiddenBufferConsumesArgumentSlot)
            slots.Add((false, false, 1));
        if (!resolved.IsStatic)
            slots.Add((false, true, 1));
        foreach (var parameter in resolved.Parameters)
            slots.Add((IsFloatingPoint(parameter), true, IntegerArgumentSlots(parameter)));
        slots.Add((false, true, 1)); // the MethodInfo argument

        var operands = new List<IOperand>(argBase + slots.Count);
        for (var i = 0; i < argBase; i++)
            operands.Add(call.Operands[i]);

        if (UsesShadowedArgumentSlots(app))
        {
            for (var slot = 0; slot < slots.Count && slot < integerRegisters.Length; slot++)
                if (slots[slot].Emit)
                    operands.Add(call.Operands[argBase + (slots[slot].IsFloat ? integerRegisters.Length + slot : slot)]);
        }
        else
        {
            // independent integer/float counters
            var (integer, floating) = (0, 0);

            foreach (var (isFloat, emit, count) in slots)
            {
                if (isFloat ? floating >= floatRegisters.Length : integer + count > integerRegisters.Length)
                    break;

                var operand = call.Operands[argBase + (isFloat ? integerRegisters.Length + floating : integer)];
                if (isFloat) floating++;
                else integer += count;
                if (emit)
                    operands.Add(operand);
            }
        }

        call.SetOperands(operands);
    }

    protected static int ArgBase(Instruction call) => call.OpCode is OpCode.CallVoid ? 1 : 2;

    private static string? RegisterName(IOperand operand) => operand switch
    {
        Register register => register.Name,
        LocalVariable { Register.Name: var name } => name,
        _ => null
    };
}
