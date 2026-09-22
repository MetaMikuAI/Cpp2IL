namespace Cpp2IL.Core.ISIL;

public struct StackOffset(int offset, int accessSize = 0) : IOperand
{
    public int Offset = offset;
    public int AccessSize = accessSize;

    public override string ToString() => $"stack[{(Offset < 0 ? ("-" + (-Offset).ToString("X")) : Offset.ToString("X"))}]";
}
