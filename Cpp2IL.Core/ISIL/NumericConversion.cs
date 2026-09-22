using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.ISIL;

internal enum NumericRounding { Truncate, Floor, Ceiling, NearestEven, NearestAway }

// Numeric conversion is not a copy: its input and result have independent types.
// ARM floating-to-integer conversions saturate, and convert NaN to zero.
internal sealed record NumericConversion(TypeAnalysisContext SourceType, TypeAnalysisContext TargetType,
    NumericRounding Rounding = NumericRounding.Truncate, int FractionalBits = 0) : IOperand;
