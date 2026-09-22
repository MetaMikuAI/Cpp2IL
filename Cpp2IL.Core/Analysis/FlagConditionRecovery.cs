using System.Collections.Generic;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Recovers high-level relational conditions from the explicit EFLAGS computations the lifter emits.
///
/// The x86 lifter models a <c>cmp</c>/<c>test</c> as a cluster of flag pseudo-registers
/// (ZF = (a-b)==0, SF = (a-b)&lt;0, OF = signed overflow, ...) and lowers each <c>jcc</c> into a
/// boolean expression over those flags. This pass recognises those canonical shapes for every
/// <see cref="OpCode.ConditionalJump"/> condition and rewrites the condition's defining instruction
/// into a single relational comparison (==, !=, &lt;, &lt;=, &gt;, &gt;=) on the original compare
/// operands. The now-orphaned flag arithmetic is removed by the dead-code pass that runs next.
///
/// Runs in SSA form, where each flag/temporary has a single, version-stable definition, so the
/// operands referenced at the branch are provably the ones captured at the compare.
///
/// ARM64 subtraction carry comparisons retain an explicit unsigned operand width.
/// Their carry/zero conditions are recovered without discarding that width.
/// Note: the x86 lifter lowers the unsigned conditions (ja/jae/jb/jbe) with the same flag expressions as
/// their signed counterparts, so they are recovered as signed comparisons too - matching the
/// existing (signed) behaviour rather than introducing a new inaccuracy.
/// </summary>
public static class FlagConditionRecovery
{
    public static void Run(MethodAnalysisContext method) => Run(method.ControlFlowGraph!);

    public static void Run(ISILControlFlowGraph cfg)
    {
        var defOf = BuildDefMap(cfg);

        foreach (var block in cfg.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                if (instruction.OpCode != OpCode.ConditionalJump)
                    continue;

                if (instruction.Operands[1] is not LocalVariable condition)
                    continue;

                if (TryUnsigned(condition, defOf, 0) is { } unsigned)
                {
                    var compare = defOf[condition];
                    compare.OpCode = unsigned.Op;
                    compare.SetOperands(compare.Operands[0], unsigned.Left, unsigned.Right, unsigned.Type);
                    continue;
                }

                if (!TryClassify(condition, defOf, out var relop, out var op0, out var op1))
                    continue;

                // Rewrite the condition's defining instruction in place into a single comparison.
                // Its destination (the condition local the branch reads) is preserved.
                var definition = defOf[condition];
                definition.OpCode = relop;
                definition.SetOperands(definition.Operands[0], op0!, op1!);
            }
        }
    }

    private static (OpCode Op, IOperand Left, IOperand Right, TypeAnalysisContext Type)? TryUnsigned(
        LocalVariable? condition, Dictionary<LocalVariable, Instruction> definitions, int depth)
    {
        if (depth > 16 || Def(condition, definitions) is not { } definition) return null;
        if (definition is { OpCode: OpCode.CheckLess, Operands: [_, var a, var b,
            TypeAnalysisContext { FullName: "System.UInt32" or "System.UInt64" } type] })
            return (OpCode.CheckLess, a, b, type);
        if (definition is { OpCode: OpCode.Not, Operands: [_, LocalVariable inner] }
            && TryUnsigned(inner, definitions, depth + 1) is { } nested)
            return (nested.Op switch
            {
                OpCode.CheckLess => OpCode.CheckGreaterOrEqual,
                OpCode.CheckGreaterOrEqual => OpCode.CheckLess,
                OpCode.CheckGreater => OpCode.CheckLessOrEqual,
                _ => OpCode.CheckGreater
            }, nested.Left, nested.Right, nested.Type);
        if (definition.OpCode is not (OpCode.And or OpCode.Or)) return null;
        for (var side = 1; side <= 2; side++)
        {
            if (TryUnsigned(AsLocal(definition.Operands[side]), definitions, depth + 1) is not { } ordered) continue;
            var other = AsLocal(definition.Operands[3 - side]);
            IOperand? z0, z1;
            bool matches;
            if (definition.OpCode == OpCode.And && ordered.Op == OpCode.CheckGreaterOrEqual)
                matches = IsNotZeroFlag(other, definitions, out z0, out z1);
            else if (definition.OpCode == OpCode.Or && ordered.Op == OpCode.CheckLess)
                matches = IsZeroFlag(other, definitions, out z0, out z1);
            else
                continue;
            if (matches && Equals(ordered.Left, z0) && Equals(ordered.Right, z1))
                return (definition.OpCode == OpCode.And ? OpCode.CheckGreater : OpCode.CheckLessOrEqual,
                    ordered.Left, ordered.Right, ordered.Type);
        }
        return null;
    }

    private static Dictionary<LocalVariable, Instruction> BuildDefMap(ISILControlFlowGraph cfg)
    {
        var defs = new Dictionary<LocalVariable, Instruction>();

        foreach (var block in cfg.Blocks)
            foreach (var instruction in block.Instructions)
                if (instruction.Destination is LocalVariable destination)
                    defs[destination] = instruction;

        return defs;
    }

    private static bool TryClassify(LocalVariable condition, Dictionary<LocalVariable, Instruction> defOf,
        out OpCode relop, out IOperand? op0, out IOperand? op1)
    {
        relop = default;

        // ZF on its own  =>  a == b   (je)
        if (IsZeroFlag(condition, defOf, out op0, out op1)) { relop = OpCode.CheckEqual; return true; }
        // SF on its own  =>  a < b    (js; exact for the common test-against-self case)
        if (IsSignFlag(condition, defOf, out op0, out op1)) { relop = OpCode.CheckLess; return true; }

        var definition = Def(condition, defOf);
        if (definition == null)
            return false;

        switch (definition.OpCode)
        {
            case OpCode.Not:
                var inner = AsLocal(definition.Operands[1]);
                if (IsZeroFlag(inner, defOf, out op0, out op1)) { relop = OpCode.CheckNotEqual; return true; }          // !ZF        => !=  (jne)
                if (IsSignFlag(inner, defOf, out op0, out op1)) { relop = OpCode.CheckGreaterOrEqual; return true; }    // !SF        => >=  (jns)
                if (IsSignEqualsOverflow(inner, defOf, out op0, out op1)) { relop = OpCode.CheckLess; return true; }    // !(SF==OF)  => <   (jl/jb)
                // Conditional selects branch on the inverse of their native condition.
                if (IsNotSignEqualsOverflow(inner, defOf, out op0, out op1)) { relop = OpCode.CheckGreaterOrEqual; return true; }
                if (Def(inner, defOf) is { OpCode: OpCode.And } greater
                    && IsSignGreater(greater, defOf, out op0, out op1)) { relop = OpCode.CheckLessOrEqual; return true; }
                if (Def(inner, defOf) is { OpCode: OpCode.Or } lessOrEqual
                    && IsSignLessOrEqual(lessOrEqual, defOf, out op0, out op1)) { relop = OpCode.CheckGreater; return true; }
                return false;

            case OpCode.CheckEqual:
                // SF == OF  =>  a >= b   (jge/jae)
                if (IsSignEqualsOverflow(condition, defOf, out op0, out op1)) { relop = OpCode.CheckGreaterOrEqual; return true; }
                return false;

            case OpCode.And:
                // (SF==OF) && !ZF  =>  a > b   (jg/ja)
                if (IsSignGreater(definition, defOf, out op0, out op1)) { relop = OpCode.CheckGreater; return true; }
                return false;

            case OpCode.Or:
                // !(SF==OF) || ZF  =>  a <= b   (jle/jbe)
                if (IsSignLessOrEqual(definition, defOf, out op0, out op1)) { relop = OpCode.CheckLessOrEqual; return true; }
                return false;

            default:
                return false;
        }
    }

    // ZF: local := CheckEqual(t, 0) where t := Subtract(a, b)
    private static bool IsZeroFlag(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        op0 = op1 = null;
        var def = Def(local, defOf);
        if (def is not { OpCode: OpCode.CheckEqual } || !IsZeroConstant(def.Operands[2]))
            return false;
        return IsSubtraction(AsLocal(def.Operands[1]), defOf, out op0, out op1);
    }

    // SF: local := CheckLess(t, 0) where t := Subtract(a, b)
    private static bool IsSignFlag(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        op0 = op1 = null;
        var def = Def(local, defOf);
        if (def is not { OpCode: OpCode.CheckLess, Operands.Count: 3 } || !IsZeroConstant(def.Operands[2]))
            return false;
        return IsSubtraction(AsLocal(def.Operands[1]), defOf, out op0, out op1);
    }

    // local := Subtract(a, b)
    private static bool IsSubtraction(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        op0 = op1 = null;
        var def = Def(local, defOf);
        if (def is not { OpCode: OpCode.Subtract })
            return false;
        op0 = def.Operands[1];
        op1 = def.Operands[2];
        return true;
    }

    // local := CheckEqual(SF, OF). Both flags must describe the same subtraction:
    // OF = ((a ^ b) & (a ^ (a - b))) < 0, SF = (a - b) < 0.
    private static bool IsSignEqualsOverflow(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        op0 = op1 = null;
        var def = Def(local, defOf);
        if (def is not { OpCode: OpCode.CheckEqual, Operands: [_, var sign, var overflow] }
            || Def(AsLocal(sign), defOf) is not { OpCode: OpCode.CheckLess, Operands: [_, LocalVariable difference, Immediate { Value: 0 }] }
            || !IsSubtraction(difference, defOf, out op0, out op1)
            || Def(AsLocal(overflow), defOf) is not { OpCode: OpCode.CheckLess, Operands: [_, var bits, Immediate { Value: 0 }] }
            || Def(AsLocal(bits), defOf) is not { OpCode: OpCode.And, Operands: [_, var ab, var ar] }
            || Def(AsLocal(ab), defOf) is not { OpCode: OpCode.Xor, Operands: [_, var a, var b] }
            || Def(AsLocal(ar), defOf) is not { OpCode: OpCode.Xor, Operands: [_, var original, var result] })
            return false;
        return Equals(a, op0) && Equals(b, op1) && Equals(original, op0) && Equals(result, difference);
    }

    // local := Not(CheckEqual(SF, OF))
    private static bool IsNotSignEqualsOverflow(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        op0 = op1 = null;
        var def = Def(local, defOf);
        if (def is not { OpCode: OpCode.Not })
            return false;
        return IsSignEqualsOverflow(AsLocal(def.Operands[1]), defOf, out op0, out op1);
    }

    // local := Not(ZF)
    private static bool IsNotZeroFlag(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        op0 = op1 = null;
        var def = Def(local, defOf);
        return def is { OpCode: OpCode.Not } && IsZeroFlag(AsLocal(def.Operands[1]), defOf, out op0, out op1);
    }

    // And((SF==OF), !ZF), in either operand order
    private static bool IsSignGreater(Instruction and, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        var left = AsLocal(and.Operands[1]);
        var right = AsLocal(and.Operands[2]);

        if (IsSignEqualsOverflow(left, defOf, out op0, out op1) && IsNotZeroFlag(right, defOf, out var z0, out var z1)
            && Equals(op0, z0) && Equals(op1, z1))
            return true;
        if (IsSignEqualsOverflow(right, defOf, out op0, out op1) && IsNotZeroFlag(left, defOf, out z0, out z1)
            && Equals(op0, z0) && Equals(op1, z1))
            return true;

        op0 = op1 = null;
        return false;
    }

    // Or(!(SF==OF), ZF), in either operand order
    private static bool IsSignLessOrEqual(Instruction or, Dictionary<LocalVariable, Instruction> defOf, out IOperand? op0, out IOperand? op1)
    {
        var left = AsLocal(or.Operands[1]);
        var right = AsLocal(or.Operands[2]);

        if (IsNotSignEqualsOverflow(left, defOf, out op0, out op1) && IsZeroFlag(right, defOf, out var z0, out var z1)
            && Equals(op0, z0) && Equals(op1, z1))
            return true;
        if (IsNotSignEqualsOverflow(right, defOf, out op0, out op1) && IsZeroFlag(left, defOf, out z0, out z1)
            && Equals(op0, z0) && Equals(op1, z1))
            return true;

        op0 = op1 = null;
        return false;
    }

    private static Instruction? Def(LocalVariable? local, Dictionary<LocalVariable, Instruction> defOf)
        => local != null && defOf.TryGetValue(local, out var def) ? def : null;

    private static LocalVariable? AsLocal(IOperand operand) => operand as LocalVariable;

    private static bool IsZeroConstant(IOperand operand) => operand is Immediate { Value: 0 };
}
