using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Analysis;

// A side-effect-free interface lookup already verified and excised by recovery.
internal sealed record NativeDisposal(Instruction Call, ulong Lookup, string Receiver);
