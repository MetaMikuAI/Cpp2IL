using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using Cpp2IL.Core.Utils.AsmResolver;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core;

public static class IlGenerator
{
    private const string HelpersNamespace = "Cpp2ILInjected";
    private const string HelpersTypeName = "Cpp2ILHelpers";
    private const string NoteIssueMethodName = "NoteDecompilerIssue";

    public static void InjectHelpersType(ApplicationAnalysisContext appContext)
    {
        var helpersType = appContext.InjectTypeIntoAllAssemblies(
            HelpersNamespace,
            HelpersTypeName,
            null,
            TypeAttributes.Public | TypeAttributes.Class | TypeAttributes.Abstract | TypeAttributes.Sealed);

        helpersType.InjectMethodToAllAssemblies(
            NoteIssueMethodName,
            appContext.SystemTypes.SystemVoidType,
            MethodAttributes.Public | MethodAttributes.Static,
            [appContext.SystemTypes.SystemStringType]);
    }

    public static void GenerateIl(MethodAnalysisContext context, MethodDefinition definition)
    {
        var assembly = context.DeclaringType!.DeclaringAssembly;
        var module = definition.DeclaringModule!;
        var factory = module.CorLibTypeFactory;

        var noteIssueContext = assembly
            .GetTypeByFullName($"{HelpersNamespace}.{HelpersTypeName}")?.Methods.FirstOrDefault(m => m.Name == NoteIssueMethodName);

        var writeLine = noteIssueContext != null
            ? noteIssueContext.ToMethodDescriptor()
            : factory.CorLibScope
                .CreateTypeReference("System", "Console")
                .CreateMemberReference("WriteLine", MethodSignature.CreateStatic(factory.Void, [factory.String]));

        // Change branch targets to instructions
        foreach (var instruction in context.ControlFlowGraph!.Blocks.SelectMany(block => block.Instructions))
        {
            if (instruction.OpCode == OpCode.Switch)
            {
                for (var i = 3; i < instruction.Operands.Count; i++)
                    if (instruction.Operands[i] is Block switchTarget && switchTarget.Instructions.Count > 0)
                        instruction.SetOperand(i, switchTarget.Instructions[0]);
                continue;
            }

            if (instruction.Operands.Count > 0 && instruction.Operands[0] is Block target)
            {
                if (target.Instructions.Count > 0)
                    instruction.SetOperand(0, target.Instructions[0]);
            }
        }

        var body = new CilMethodBody()
        {
            InitializeLocals = true, // Without this ILSpy does: CompilerServices.Unsafe.SkipInit(out object obj);
            ComputeMaxStackOnBuild = false // There's stack imbalance somewhere, but this works for now
        };

        definition.CilMethodBody = body;

        // Make sure context.Locals actually has all locals (idk why it doesn't sometimes)
        foreach (var operand in context.ControlFlowGraph.Instructions.SelectMany(i => i.Operands))
        {
            LocalVariable? local = null;

            if (operand is FieldReference field)
                local = field.Local;

            if (operand is LocalVariable local2)
                local = local2;

            if (operand is MemoryOperand memory && memory.Base is LocalVariable local3)
                local = local3;

            var elementOperand = operand is AddressOf { Target: ArrayAccess elementAddress } ? elementAddress : operand;

            if (elementOperand is ArrayAccess arrayAccess)
            {
                local = arrayAccess.Array;

                if (arrayAccess.Index is LocalVariable index && !context.Locals.Contains(index))
                    context.Locals.Add(index);
            }

            if (operand is ArrayLength arrayLength)
                local = arrayLength.Array;

            if (operand is AddressOf { Target: LocalVariable addressed })
                local = addressed;

            if (local != null && !context.Locals.Contains(local))
                context.Locals.Add(local);
        }

        // Map ISIL locals to IL
        Dictionary<LocalVariable, CilLocalVariable> locals = [];
        foreach (var local in context.Locals)
        {
            TypeSignature ilType;

            // Use object if type couldn't be determined, or if it's void, which no locals sig can hold
            if (local.Type != null && local.Type != context.AppContext.SystemTypes.SystemVoidType)
                ilType = local.Type.ToTypeSignature();
            else
                ilType = module.CorLibTypeFactory.Object;

            var ilLocal = new CilLocalVariable(ilType);
            body.LocalVariables.Add(ilLocal);
            locals.Add(local, ilLocal);
        }

        /* foreach (var instruction in context.ControlFlowGraph!.Instructions)
        {
            body.Instructions.Add(CilOpCodes.Ldstr, instruction.ToString());
            body.Instructions.Add(CilOpCodes.Call, _importer!.ImportMethod(_writeLine!));
        }
        body.Instructions.Add(CilOpCodes.Ldstr, "-------------------------------------------------------------------------");
        body.Instructions.Add(CilOpCodes.Call, _importer!.ImportMethod(_writeLine!)); */

        // Generate IL
        Dictionary<Instruction, List<CilInstruction>> instructionMap = [];
        Dictionary<Block, CilInstruction> blockEntryMap = [];
        List<(CilInstruction BranchInstruction, Block TargetBlock)> pendingBlockBranchFixups = [];

        foreach (var block in context.ControlFlowGraph!.Blocks)
        {
            if (block == context.ControlFlowGraph.EntryBlock || block == context.ControlFlowGraph.ExitBlock)
                continue;

            if (block.Instructions.Count == 0)
                continue;

            foreach (var instruction in block.Instructions)
            {
                var generated = GenerateInstructions(instruction, context, definition, locals, writeLine);
                instructionMap.Add(instruction, generated);

                if (!blockEntryMap.ContainsKey(block) && generated.Count > 0)
                    blockEntryMap[block] = generated[0];
            }

            var lastInstruction = block.Instructions.Last();
            
            if (lastInstruction.OpCode == OpCode.ConditionalJump)
            {
                var trueTarget = TryResolveJumpTargetBlock(lastInstruction, context.ControlFlowGraph);
                var falseSuccessor = block.Successors.FirstOrDefault(s => s != trueTarget && s != context.ControlFlowGraph.ExitBlock);
                if (falseSuccessor == null) continue;
                var bridge = new CilInstruction(CilOpCodes.Br, new CilInstructionLabel());
                definition.CilMethodBody!.Instructions.Add(bridge);
                pendingBlockBranchFixups.Add((bridge, falseSuccessor));
            }

            else if (lastInstruction.OpCode is not (OpCode.Jump or OpCode.Return or OpCode.IndirectJump or OpCode.Switch))
            {
                var successor = block.Successors.FirstOrDefault(s => s != context.ControlFlowGraph.ExitBlock);
                if (successor == null) continue;
                var bridge = new CilInstruction(CilOpCodes.Br, new CilInstructionLabel());
                definition.CilMethodBody!.Instructions.Add(bridge);
                pendingBlockBranchFixups.Add((bridge, successor));
            }
        }
        // Set IL branch targets
        foreach (var kvp in instructionMap)
        {
            var instruction = kvp.Key;
            var il = kvp.Value;

            if (instruction.OpCode == OpCode.Switch)
            {
                var targets = instruction.Operands.Skip(3)
                    .Cast<Instruction>()
                    .Select(target => (ICilLabel)new CilInstructionLabel(instructionMap[target][0]))
                    .ToArray();
                il.First(candidate => candidate.OpCode == CilOpCodes.Switch).Operand = targets.Skip(1).ToArray();
                il.First(candidate => candidate.OpCode == CilOpCodes.Br).Operand = targets[0];
            }
            else if (instruction.OpCode == OpCode.Jump || instruction.OpCode == OpCode.ConditionalJump)
            {
                var ilBranch = il.First(i => i.OpCode == CilOpCodes.Br || i.OpCode == CilOpCodes.Brtrue);

                if (instruction.Operands[0] is Block targetBlock)
                {
                    context.AddWarning($"Branch target block not in cfg: {instruction} ({targetBlock})");
                    ilBranch.OpCode = CilOpCodes.Nop;
                    ilBranch.Operand = null;
                    continue;
                }

                var target = (Instruction)instruction.Operands[0];

                if (!instructionMap.ContainsKey(target))
                {
                    context.AddWarning($"Branch target not in ISIL to IL map: {instruction} --- {target}");
                    ilBranch.OpCode = CilOpCodes.Nop;
                    ilBranch.Operand = null;
                    continue;
                }

                ilBranch.Operand = new CilInstructionLabel(instructionMap[target][0]);
            }
        }
        
        foreach (var (branchInstruction, targetBlock) in pendingBlockBranchFixups)
        {
            var target = ResolveBlockEntryInstruction(targetBlock, blockEntryMap);
            if (target == null)
            {
                context.AddWarning($"Unable to resolve branch target block: {targetBlock}");
                branchInstruction.OpCode = CilOpCodes.Nop;
                branchInstruction.Operand = null;
                continue;
            }

            branchInstruction.Operand = new CilInstructionLabel(target);
        }

        // Add analysis warnings
        var instructions = body.Instructions;
        foreach (var warning in context.AnalysisWarnings)
        {
            instructions.Add(CilOpCodes.Ldstr, Diagnostic("Warning: " + warning));
            instructions.Add(CilOpCodes.Call, writeLine);
        }

        NormalizeDelegateConstruction(definition);
        NormalizeLinqGenericInstantiations(definition);
        NormalizeLambdaNullChecks(definition);
        ForeachRecovery.Run(definition);
    }

    private static readonly HashSet<string> LinqMethodNames =
    [
        "Select", "Where", "Any", "All", "First", "FirstOrDefault", "Single", "SingleOrDefault", "Last", "LastOrDefault",
        "Count", "Min", "Max", "Sum", "Average", "Contains", "ToArray", "ToList", "ElementAt", "ElementAtOrDefault",
        "Skip", "Take", "Concat", "OrderBy", "OrderByDescending", "SelectMany"
    ];

    /// <summary>
    /// Cpp2IL sometimes emits a delegate constructor as an instance call (allocated receiver + ldftn + call .ctor).
    /// The CLR/ILSpy expect <c>newobj</c>, and the extra receiver breaks ILSpy's cached-lambda pattern recognition.
    /// </summary>
    private static void NormalizeDelegateConstruction(MethodDefinition definition)
    {
        var instructions = definition.CilMethodBody!.Instructions;

        for (var i = 0; i < instructions.Count; i++)
        {
            var ctorCall = instructions[i];
            if (ctorCall.OpCode != CilOpCodes.Call || ctorCall.Operand is not IMethodDescriptor ctorMethod)
                continue;

            if (ctorMethod.Name != ".ctor" || !IsDelegateTypeName(ctorMethod.DeclaringType?.Name?.ToString()))
                continue;

            // Pattern: ldloc receiver / ldsfld <>9 / ldftn lambda / call Delegate::.ctor
            if (i < 3)
                continue;

            var ldftn = instructions[i - 1];
            var singleton = instructions[i - 2];
            var receiver = instructions[i - 3];

            if (ldftn.OpCode != CilOpCodes.Ldftn
                || singleton.OpCode != CilOpCodes.Ldsfld
                || singleton.Operand is not IFieldDescriptor singletonField
                || singletonField.Name?.ToString() != "<>9"
                || receiver.OpCode != CilOpCodes.Ldloc)
                continue;

            // newobj takes only (object, native int); drop the pre-allocated receiver. Only rewrite the
            // canonical cached-delegate shape: after "stsfld <>9__N" comes either another receiver
            // load/consumer local or a branch. Anything else (unrelated IL between cache store and
            // consumer) is left untouched so we don't leave a delegate on the stack.
            var receiverLocal = receiver.Operand as CilLocalVariable;
            var afterStoreDuplicate = instructions[i + 1];
            var cacheStore = instructions[i + 2];
            var firstAfterCache = i + 3 < instructions.Count ? instructions[i + 3] : null;

            var isCanonicalAfterStore = afterStoreDuplicate.OpCode == CilOpCodes.Ldloc
                                        && cacheStore.OpCode == CilOpCodes.Stsfld
                                        && cacheStore.Operand is IFieldDescriptor { } cacheField
                                        && cacheField.Name?.ToString().StartsWith("<>9__") == true
                                        && firstAfterCache != null
                                        && (firstAfterCache.OpCode == CilOpCodes.Br
                                            || firstAfterCache.OpCode == CilOpCodes.Brtrue
                                            || firstAfterCache.OpCode == CilOpCodes.Brfalse
                                            || firstAfterCache.OpCode == CilOpCodes.Ret
                                            || firstAfterCache.OpCode == CilOpCodes.Nop
                                            || (firstAfterCache.OpCode == CilOpCodes.Ldloc && ReferenceEquals(firstAfterCache.Operand, receiverLocal)));

            if (!isCanonicalAfterStore)
                continue;

            receiver.OpCode = CilOpCodes.Nop;
            receiver.Operand = null;
            ctorCall.OpCode = CilOpCodes.Newobj;

            afterStoreDuplicate.OpCode = CilOpCodes.Nop;
            afterStoreDuplicate.Operand = null;
            instructions.Insert(i + 2, new CilInstruction(CilOpCodes.Dup));

            // Nop every duplicated receiver load between the cache store and the next branch so the
            // single delegate copy left by dup/stsfld flows into the consumer local.
            var consumedByStore = false;
            for (var j = i + 3; j < instructions.Count; j++)
            {
                var candidate = instructions[j];
                if (candidate.OpCode == CilOpCodes.Br || candidate.OpCode == CilOpCodes.Brtrue
                    || candidate.OpCode == CilOpCodes.Brfalse || candidate.OpCode == CilOpCodes.Ret)
                {
                    // No consumer local follows the cache store; discard the copy dup left behind.
                    if (!consumedByStore)
                        instructions.Insert(j, new CilInstruction(CilOpCodes.Pop));
                    break;
                }

                if (candidate.OpCode == CilOpCodes.Stloc)
                    consumedByStore = true;

                if (candidate.OpCode == CilOpCodes.Ldloc && ReferenceEquals(candidate.Operand, receiverLocal))
                {
                    candidate.OpCode = CilOpCodes.Nop;
                    candidate.Operand = null;
                }
            }
        }
    }

    private static bool IsDelegateTypeName(string? name)
        => name is not null && (name.StartsWith("Func`") || name.StartsWith("Action`"));

    private static TypeSignature? GetFieldType(IFieldDescriptor? field) =>
        field switch
        {
            FieldDefinition fieldDefinition => fieldDefinition.Signature?.FieldType,
            MemberReference memberReference when memberReference.Signature is FieldSignature signature => signature.FieldType,
            _ => null
        };

    private static bool TryGetDelegateTypeArguments(IFieldDescriptor? field, out TypeSignature[] delegateArgs, out TypeSignature? delegateType)
    {
        delegateArgs = [];
        delegateType = GetFieldType(field);

        if (delegateType is GenericInstanceTypeSignature generic
            && IsDelegateTypeName(generic.GenericType?.Name?.ToString()))
        {
            delegateArgs = generic.TypeArguments.ToArray();
            return true;
        }

        return false;
    }

    /// <summary>
    /// LINQ extension calls occasionally get instantiated with object placeholders (e.g. <c>Select&lt;object,int&gt;</c>)
    /// instead of the cached delegate's real argument types. Recover the instantiation from the <c>&lt;&gt;9__N</c>
    /// cache field that feeds the call, and retype the selector local so ILSpy can fold the delegate back into a lambda.
    /// </summary>
    private static void NormalizeLinqGenericInstantiations(MethodDefinition definition)
    {
        var instructions = definition.CilMethodBody!.Instructions;

        for (var i = 0; i < instructions.Count; i++)
        {
            var call = instructions[i];
            if (call.OpCode != CilOpCodes.Call || call.Operand is not MethodSpecification specification)
                continue;

            if (!LinqMethodNames.Contains(specification.Name ?? "") || specification.Signature is not { } signature)
                continue;

            var selector = i > 0 ? instructions[i - 1] : null;
            if (selector == null || selector.OpCode != CilOpCodes.Ldloc || selector.Operand is not CilLocalVariable selectorLocal)
                continue;

            // Walk back over the cached-delegate pattern to find the <>9__N field whose type knows the real args.
            TypeSignature[]? delegateArgs = null;
            TypeSignature? delegateType = null;

            for (var j = i - 1; j >= Math.Max(0, i - 60); j--)
            {
                if (instructions[j].Operand is not IFieldDescriptor candidateField)
                    continue;

                var candidateName = candidateField.Name?.ToString();
                if (string.IsNullOrEmpty(candidateName) || !candidateName.StartsWith("<>9__"))
                    continue;

                if (!TryGetDelegateTypeArguments(candidateField, out var candidateArgs, out var candidateType))
                    continue;

                delegateArgs = candidateArgs;
                delegateType = candidateType;
                break;
            }

            if (delegateArgs == null)
                continue;

            // Func<TArg,TResult> maps to Select<TArg,TResult>; Func<TArg,bool> maps to Where/Any<TArg>.
            var targetArgCount = signature.TypeArguments.Count;
            var newArgs = targetArgCount switch
            {
                2 when delegateArgs.Length >= 2 => new[] { delegateArgs[0], delegateArgs[1] },
                1 when delegateArgs.Length >= 1 => new[] { delegateArgs[0] },
                _ => null
            };

            if (newArgs == null)
                continue;

            specification.Signature = new GenericInstanceMethodSignature(newArgs);

            if (delegateType != null)
                selectorLocal.VariableType = delegateType;
        }
    }

    /// <summary>
    /// IL2CPP null checks can be emitted as "build NullReferenceException, store it, and return the exception
    /// object as the method's value". Replace the terminal copy with a real throw.
    /// </summary>
    private static void NormalizeLambdaNullChecks(MethodDefinition definition)
    {
        if (definition.Name?.ToString().Contains("b__") != true)
            return;

        var instructions = definition.CilMethodBody!.Instructions;

        for (var i = 0; i < instructions.Count; i++)
        {
            if (instructions[i].OpCode != CilOpCodes.Newobj || instructions[i].Operand is not IMethodDescriptor ctor)
                continue;

            if (ctor.Name != ".ctor" || ctor.DeclaringType?.Name != "NullReferenceException")
                continue;

            ConvertReturnedExceptionToThrow(instructions, i);
        }
    }

    /// <summary>
    /// Fixes the invalid "return the exception object as the method's value" IL that Cpp2IL emits for
    /// IL2CPP null checks.
    /// </summary>
    private static void ConvertReturnedExceptionToThrow(CilInstructionCollection instructions, int newObjIndex)
    {
        if (newObjIndex + 3 >= instructions.Count)
            return;

        var store = instructions[newObjIndex + 1];
        var load = instructions[newObjIndex + 2];
        var ret = instructions[newObjIndex + 3];

        if (store.OpCode != CilOpCodes.Stloc || store.Operand is not CilLocalVariable exceptionLocal
            || load.OpCode != CilOpCodes.Ldloc || load.Operand is not CilLocalVariable loadedLocal
            || !ReferenceEquals(exceptionLocal, loadedLocal)
            || ret.OpCode != CilOpCodes.Ret)
            return;

        store.OpCode = CilOpCodes.Nop;
        store.Operand = null;
        load.OpCode = CilOpCodes.Nop;
        load.Operand = null;
        ret.OpCode = CilOpCodes.Throw;
        ret.Operand = null;
    }

    // Limit so we don't run into the 16mb limit (see AsmResolver issue #775)
    private static string Diagnostic(string message) 
        => message.Length <= 250 ? message : message[..250] + "…";
    
    private static Block? TryResolveJumpTargetBlock(Instruction jumpInstruction, ISILControlFlowGraph cfg)
    {
        if (jumpInstruction.Operands.Count == 0)
            return null;

        if (jumpInstruction.Operands[0] is Block targetBlock)
            return targetBlock;

        if (jumpInstruction.Operands[0] is Instruction targetInstruction)
            return cfg.FindBlockByInstruction(targetInstruction);

        return null;
    }

    private static CilInstruction? ResolveBlockEntryInstruction(Block block,
        Dictionary<Block, CilInstruction> blockEntryMap, HashSet<Block>? visited = null)
    {
        if (blockEntryMap.TryGetValue(block, out var target))
            return target;

        visited ??= [];
        if (!visited.Add(block))
            return null;

        foreach (var successor in block.Successors)
        {
            var resolved = ResolveBlockEntryInstruction(successor, blockEntryMap, visited);
            if (resolved != null)
                return resolved;
        }
        return null;
    }

    private static List<CilInstruction> GenerateInstructions(Instruction instruction, MethodAnalysisContext context,
        MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        var body = method.CilMethodBody!;
        var instructions = body.Instructions;
        var currentCount = instructions.Count;
        var startIndex = instructions.Count;

        var module = method.DeclaringModule!;

        switch (instruction.OpCode)
        {
            case OpCode.Invalid:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Invalid instruction: {instruction}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.NotImplemented:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Not implemented instruction: {instruction.Operands[0]}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.Interrupt:
            case OpCode.Nop:
                instructions.Add(CilOpCodes.Nop);
                break;

            case OpCode.Move:
                // Native aggregate zeroing can collapse to a scalar Move after adjacent ARM64
                // stack slots are reconnected into one value-type local. A scalar ldc.i4.0 cannot
                // be stored into that local in managed IL; initialize the aggregate explicitly.
                if (instruction.Operands is [LocalVariable { Type: { IsValueType: true } valueType } zeroed, var zero]
                    && valueType.Type is Il2CppTypeEnum.IL2CPP_TYPE_VALUETYPE or Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST
                    && IsZeroConstant(zero))
                {
                    instructions.Add(CilOpCodes.Ldloca, locals[zeroed]);
                    instructions.Add(CilOpCodes.Initobj, valueType.ToTypeSignature().ToTypeDefOrRef());
                    break;
                }

                if (instruction.Operands[0] is FieldReference field) // stfld takes instance before value so LoadOperand StoreToOperand doesn't work
                {
                    if (!field.Field.IsStatic)
                    {
                        LoadLocal(field.Local, method, locals);

                        if (field.ContainingField is { } containing)
                            instructions.Add(CilOpCodes.Ldflda, containing.ToFieldDescriptor());
                    }

                    LoadOperand(instruction.Operands[1], method, locals, writeLine, field.Field.FieldType);
                    instructions.Add(field.Field.IsStatic ? CilOpCodes.Stsfld : CilOpCodes.Stfld, field.Field.ToFieldDescriptor());
                    break;
                }

                // stelem needs array and index before the value, so like stfld it can't go through LoadOperand/StoreToOperand.
                // This also lets ILSpy handle it as a proper array initializer
                if (instruction.Operands[0] is ArrayAccess { Array.Type: SzArrayTypeAnalysisContext { ElementType: { } stored } } target)
                {
                    LoadLocal(target.Array, method, locals);
                    LoadOperand(target.Index, method, locals, writeLine);
                    LoadOperand(instruction.Operands[1], method, locals, writeLine, stored);
                    instructions.Add(CilOpCodes.Stelem, stored.ToTypeSignature().ToTypeDefOrRef());
                    break;
                }

                LoadOperand(instruction.Operands[1], method, locals, writeLine, DestinationType(instruction.Operands[0]));
                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.NewArr:
                if (instruction.Operands is [_, SzArrayTypeAnalysisContext { ElementType: { } newArrayElement }, { } length])
                {
                    LoadOperand(length, method, locals, writeLine);
                    instructions.Add(CilOpCodes.Newarr, newArrayElement.ToTypeSignature().ToTypeDefOrRef());
                }
                else
                    instructions.Add(CilOpCodes.Ldnull);

                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.Newobj:
                // Try and fuse our Newobj + the follow up constructor CallVoid into one IL newobj.
                // If we can't, just fall back to an Ldnull.
                if (FindConstructorCall(context, instruction) is { Operands: [MethodAnalysisContext constructor, _, ..] } constructorCall)
                {
                    // Operands run [ctor, newObject, arguments..., methodInfo], so take only as many as
                    // the constructor declares (i.e. drop methodInfo)
                    var constructorArgs = constructorCall.Operands.Skip(ConstructorReceiverIndex(constructorCall) + 1).Take(constructor.Parameters.Count).ToList();
                    for (var i = 0; i < constructorArgs.Count; i++)
                        LoadOperand(constructorArgs[i], method, locals, writeLine, constructor.Parameters[i].ParameterType);

                    instructions.Add(CilOpCodes.Newobj, constructor.ToMethodDescriptor());
                    StoreToOperand(instruction.Operands[0], method, locals, writeLine);

                    constructorCall.OpCode = OpCode.Nop;
                    constructorCall.SetOperands();
                }
                else if (instruction.Operands is [_, TypeAnalysisContext allocatedType] && allocatedType.Methods.FirstOrDefault(m => m is { Name: ".ctor", Parameters.Count: 0 }) is { } parameterlessCtor)
                {
                    // Nothing to fuse with, so the allocation was self-contained. The type is still right, so construct it bare.
                    instructions.Add(CilOpCodes.Newobj, parameterlessCtor.ToMethodDescriptor());
                    StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                }
                else
                {
                    instructions.Add(CilOpCodes.Ldnull);
                    StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                }
                break;

            case OpCode.Box:
                if (instruction.Operands is [_, TypeAnalysisContext boxedType, var boxedValue])
                {
                    // il2cpp_value_box takes the value by address, but IL boxes it by value
                    LoadOperand(boxedValue is AddressOf { Target: LocalVariable byRef } ? byRef : boxedValue, method, locals, writeLine, boxedType);
                    instructions.Add(CilOpCodes.Box, boxedType.ToTypeSignature().ToTypeDefOrRef());
                }
                else
                    instructions.Add(CilOpCodes.Ldnull);

                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.Throw:
                if (instruction.Operands is [TypeAnalysisContext exceptionType]
                    && exceptionType.Methods.FirstOrDefault(m => m.Name == ".ctor" && m.Parameters.Count == 0) is { } exceptionCtor)
                    instructions.Add(CilOpCodes.Newobj, exceptionCtor.ToMethodDescriptor());
                else if (instruction.Operands is [LocalVariable or FieldReference])
                    LoadOperand(instruction.Operands[0], method, locals, writeLine); // an already-constructed exception
                else
                    instructions.Add(CilOpCodes.Ldnull);

                instructions.Add(CilOpCodes.Throw);
                break;

            case OpCode.Phi:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Phi opcodes should not exist at this point in decompilation ({instruction})"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.Call:
            case OpCode.CallVoid:
                if (instruction.Operands[0] is not MethodAnalysisContext targetMethod)
                {
                    if (instruction.Operands[0] is Immediate targetAddress)
                        instructions.Add(CilOpCodes.Ldstr, $"Method not found @{targetAddress.UnsignedValue:X}");
                    else // Probably key function. Just the target, the full operand dump is huge and blows the 16MB #US heap limit
                        instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Unknown call target operand: {instruction.Operands[0]}"));

                    instructions.Add(CilOpCodes.Call, writeLine);
                    break;
                }

                var importedMethod = targetMethod.ToMethodDescriptor();

                var thisParamIndex = instruction.OpCode == OpCode.Call ? 2 : 1;

                if (!targetMethod.IsStatic) // Load 'this' param
                {
                    if ((instruction.Operands.Count - 1) >= thisParamIndex)
                        LoadOperand(instruction.Operands[thisParamIndex], method, locals, writeLine, targetMethod.DeclaringType);
                    else
                    {
                        instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Non static method called without 'this' param ({instruction})"));
                        instructions.Add(CilOpCodes.Call, writeLine);
                        instructions.Add(CilOpCodes.Ldnull);
                    }
                }

                // Load normal params
                var callParamIndex = instruction.OpCode == OpCode.Call ? (targetMethod.IsStatic ? 2 : 3) : (targetMethod.IsStatic ? 1 : 2);
                // A call whose target was only identified after lifting still carries the operands the
                // unknown-callee convention gave it, which may be fewer than the method actually takes.
                // The stack still has to match the signature, so anything missing gets a placeholder.
                var availableArgs = instruction.Operands.Count - callParamIndex;
                for (var i = 0; i < targetMethod.Parameters.Count; i++)
                {
                    var parameterType = targetMethod.Parameters[i].ParameterType;

                    if (i < availableArgs)
                        LoadOperand(instruction.Operands[callParamIndex + i], method, locals, writeLine, parameterType);
                    else
                        PushDefaultOf(parameterType, instructions);
                }

                instructions.Add(CilOpCodes.Call, importedMethod);

                // the lifter's guess at whether the callee returns anything can disagree with the
                // signature we later resolved, so go by the signature and balance the stack
                if (!targetMethod.IsVoid)
                {
                    if (instruction.OpCode == OpCode.Call)
                        StoreToOperand(instruction.Operands[1], method, locals, writeLine);
                    else
                        instructions.Add(CilOpCodes.Pop);
                }

                break;

            case OpCode.IndirectCall:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Indirect call: {instruction.Operands[0]} (should have been resolved before IL gen)"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.Return:
                if (!context.IsVoid)
                {
                    if (instruction.Operands.Count == 1)
                        LoadOperand(instruction.Operands[0], method, locals, writeLine, context.ReturnType);
                    else
                        instructions.Add(CilOpCodes.Ldnull); // ret still pops a value even if we lost track of it
                }
                instructions.Add(CilOpCodes.Ret);
                break;

            case OpCode.Jump:
                instructions.Add(CilOpCodes.Br, new CilInstructionLabel());
                break;

            case OpCode.ConditionalJump:
                LoadOperand(instruction.Operands[1], method, locals, writeLine);
                instructions.Add(CilOpCodes.Brtrue, new CilInstructionLabel());
                break;

            case OpCode.IndirectJump:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Indirect jump: {instruction.Operands[0]} (should have been resolved before IL gen)"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.Switch:
                LoadSwitchSelector(instruction, context, method, locals, writeLine);
                instructions.Add(CilOpCodes.Switch, Array.Empty<ICilLabel>());
                instructions.Add(CilOpCodes.Br, new CilInstructionLabel());
                break;

            case OpCode.ShiftStack:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Stack shift: {instruction} (stack analysis should have removed these)"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;

            case OpCode.CheckEqual:
            case OpCode.CheckGreater:
            case OpCode.CheckLess:
            case OpCode.CheckNotEqual:
            case OpCode.CheckGreaterOrEqual:
            case OpCode.CheckLessOrEqual:

            case OpCode.Add:
            case OpCode.Subtract:
            case OpCode.Multiply:
            case OpCode.Divide:
            case OpCode.Modulo:

            case OpCode.ShiftLeft:
            case OpCode.ShiftRight:

            case OpCode.And:
            case OpCode.Or:
            case OpCode.Xor:
                // klass pointer read => GetType
                if (instruction.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual
                    && TryEmitExactTypeComparison(instruction, method, locals, writeLine))
                    break;

                // Float arithmetic on a promoted integer operand needs an explicit conversion, so both
                // operands are coerced to the (float) result type. A no-op when they already match.
                var floatConversion = FloatArithmeticConversion(instruction);

                LoadOperand(instruction.Operands[1], method, locals, writeLine);
                if (floatConversion is { } conv1)
                    instructions.Add(conv1);
                LoadOperand(instruction.Operands[2], method, locals, writeLine);
                if (floatConversion is { } conv2)
                    instructions.Add(conv2);

                switch (instruction.OpCode)
                {
                    case OpCode.CheckEqual: instructions.Add(CilOpCodes.Ceq); break;
                    case OpCode.CheckGreater: instructions.Add(CilOpCodes.Cgt); break;
                    case OpCode.CheckLess: instructions.Add(CilOpCodes.Clt); break;

                    // a != b  ==  (a == b) == 0
                    case OpCode.CheckNotEqual:
                        instructions.Add(CilOpCodes.Ceq);
                        instructions.Add(CilOpCodes.Ldc_I4_0);
                        instructions.Add(CilOpCodes.Ceq);
                        break;
                    // a >= b  ==  !(a < b)
                    case OpCode.CheckGreaterOrEqual:
                        instructions.Add(CilOpCodes.Clt);
                        instructions.Add(CilOpCodes.Ldc_I4_0);
                        instructions.Add(CilOpCodes.Ceq);
                        break;
                    // a <= b  ==  !(a > b)
                    case OpCode.CheckLessOrEqual:
                        instructions.Add(CilOpCodes.Cgt);
                        instructions.Add(CilOpCodes.Ldc_I4_0);
                        instructions.Add(CilOpCodes.Ceq);
                        break;

                    case OpCode.Add: instructions.Add(CilOpCodes.Add); break;
                    case OpCode.Subtract: instructions.Add(CilOpCodes.Sub); break;
                    case OpCode.Multiply: instructions.Add(CilOpCodes.Mul); break;
                    case OpCode.Divide: instructions.Add(CilOpCodes.Div); break;
                    case OpCode.Modulo: instructions.Add(CilOpCodes.Rem); break;

                    case OpCode.ShiftLeft: instructions.Add(CilOpCodes.Shl); break;
                    case OpCode.ShiftRight: instructions.Add(CilOpCodes.Shr); break;

                    case OpCode.And: instructions.Add(CilOpCodes.And); break;
                    case OpCode.Or: instructions.Add(CilOpCodes.Or); break;
                    case OpCode.Xor: instructions.Add(CilOpCodes.Xor); break;
                }

                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            case OpCode.Not:
            case OpCode.Negate:
                LoadOperand(instruction.Operands[1], method, locals, writeLine);

                if (instruction.OpCode == OpCode.Negate)
                    instructions.Add(CilOpCodes.Neg);
                else if (IsBoolean(instruction.Operands[1], context))
                {
                    instructions.Add(CilOpCodes.Ldc_I4_0);
                    instructions.Add(CilOpCodes.Ceq);
                }
                else
                    instructions.Add(CilOpCodes.Not);

                StoreToOperand(instruction.Operands[0], method, locals, writeLine);
                break;

            default:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Unknown instruction: {instruction}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                break;
        }

        return instructions.ToList().GetRange(startIndex, instructions.Count - startIndex); // Return added IL
    }
    
    private static int ConstructorReceiverIndex(Instruction constructorCall) => constructorCall.OpCode == OpCode.CallVoid ? 1 : 2;

    // Try find the follow up CallVoid for a constructor, after a Newobj.
    private static Instruction? FindConstructorCall(MethodAnalysisContext context, Instruction newobj)
    {
        var newObject = newobj.Operands[0];

        // The allocation and the constructor call routinely end up in different blocks
        var instructions = context.ControlFlowGraph!.Instructions;
        var index = instructions.IndexOf(newobj);

        if (index < 0)
            return null;

        for (var i = index + 1; i < instructions.Count; i++)
        {
            var candidate = instructions[i];

            if (candidate is not { OpCode: OpCode.Call or OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: ".ctor" }, ..] })
                continue;

            var receiver = ConstructorReceiverIndex(candidate);

            if (candidate.Operands.Count > receiver && ReferenceEquals(candidate.Operands[receiver], newObject))
                return candidate;
        }

        return null;
    }

    private static CilOpCode? FloatArithmeticConversion(Instruction instruction)
    {
        if (instruction.OpCode is not (OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide or OpCode.Modulo))
            return null;

        return (instruction.Operands[0] as LocalVariable)?.Type?.FullName switch
        {
            "System.Single" => CilOpCodes.Conv_R4,
            "System.Double" => CilOpCodes.Conv_R8,
            _ => null,
        };
    }

    private static void LoadOperand(IOperand operand, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine,
        TypeAnalysisContext? expectedType = null)
    {
        var instructions = method.CilMethodBody!.Instructions;

        var module = method.DeclaringModule!;

        // A null reference reaches us as an integer zero, which would otherwise be emitted as a literal 0
        // and read back as a cast from a number.
        if (expectedType is { IsValueType: false } && IsZeroConstant(operand))
        {
            instructions.Add(CilOpCodes.Ldnull);
            return;
        }

        switch (operand)
        {
            case Immediate { Value: >= int.MinValue and <= int.MaxValue } immediate:
                instructions.Add(CilOpCodes.Ldc_I4, (int)immediate.Value);
                break;
            case Immediate immediate:
                instructions.Add(CilOpCodes.Ldc_I8, immediate.Value);
                break;
            case FloatLiteral f:
                instructions.Add(CilOpCodes.Ldc_R4, f.Value);
                break;
            case DoubleLiteral d:
                instructions.Add(CilOpCodes.Ldc_R8, d.Value);
                break;
            case StringLiteral s:
                instructions.Add(CilOpCodes.Ldstr, s.Value);
                break;
            case LocalVariable local:
                LoadLocal(local, method, locals);
                break;
            case ArrayLength arrayLength:
                LoadLocal(arrayLength.Array, method, locals);
                instructions.Add(CilOpCodes.Ldlen);
                instructions.Add(CilOpCodes.Conv_I4);
                break;
            case AddressOf { Target: LocalVariable addressed }:
                instructions.Add(CilOpCodes.Ldloca, locals[addressed]);
                break;
            case AddressOf { Target: ArrayAccess elementAddress }:
                LoadLocal(elementAddress.Array, method, locals);
                LoadOperand(elementAddress.Index, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldelema,
                    ((SzArrayTypeAnalysisContext)elementAddress.Array.Type!).ElementType.ToTypeSignature().ToTypeDefOrRef());
                break;
            case ArrayAccess arrayAccess:
                LoadLocal(arrayAccess.Array, method, locals);
                LoadOperand(arrayAccess.Index, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldelem,
                    ((SzArrayTypeAnalysisContext)arrayAccess.Array.Type!).ElementType.ToTypeSignature().ToTypeDefOrRef());
                break;
            case FieldReference field:
                if (field.Field.IsStatic)
                {
                    instructions.Add(CilOpCodes.Ldsfld, field.Field.ToFieldDescriptor());
                    break;
                }

                LoadLocal(field.Local, method, locals);
                if (field.ContainingField is { } containing)
                {
                    instructions.Add(CilOpCodes.Ldflda, containing.ToFieldDescriptor());
                    instructions.Add(CilOpCodes.Ldfld, field.Field.ToFieldDescriptor());
                }
                else
                    instructions.Add(CilOpCodes.Ldfld, field.Field.ToFieldDescriptor());
                break;
            case MemoryOperand memory:
                if (memory.Index == null && memory.Addend == 0 && memory.Scale == 0
                    && memory.Base is LocalVariable local2)
                {
                    LoadLocal(local2, method, locals);

                    // A load through a managed pointer (byref) dereferences it to yield the referent.
                    if (local2.Type is ByRefTypeAnalysisContext { ElementType: { } referent })
                        instructions.Add(referent.IsValueType
                            ? new CilInstruction(CilOpCodes.Ldobj, referent.ToTypeSignature().ToTypeDefOrRef())
                            : new CilInstruction(CilOpCodes.Ldind_Ref));
                    break;
                }
                instructions.Add(CilOpCodes.Ldstr, Diagnostic("Unmanaged memory load: " + operand));
                instructions.Add(CilOpCodes.Call, writeLine);
                instructions.Add(CilOpCodes.Ldc_I4_0);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            case RuntimeMethodInfoAnalysisContext runtimeMethod:
                // A delegate constructor takes its target as a native pointer, which is exactly ldftn.
                if (expectedType?.FullName == "System.IntPtr")
                {
                    instructions.Add(CilOpCodes.Ldftn, runtimeMethod.RepresentedMethod.ToMethodDescriptor());
                    break;
                }

                //Not fully implemented, these basically shouldn't actually ever exist in the final IL.
                instructions.Add(CilOpCodes.Ldc_I4_0);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            case RuntimeFieldInfoAnalysisContext runtimeField:
                // fieldof(F), e.g. the handle InitializeArray takes.
                if (expectedType?.FullName == "System.RuntimeFieldHandle")
                {
                    instructions.Add(CilOpCodes.Ldtoken, runtimeField.RepresentedField.ToFieldDescriptor());
                    break;
                }

                instructions.Add(CilOpCodes.Ldc_I4_0);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            case RuntimeClassTypeAnalysisContext or RgctxTableTypeAnalysisContext
                or MethodRgctxTableTypeAnalysisContext or StaticFieldStorageTypeAnalysisContext:
                instructions.Add(CilOpCodes.Ldc_I4_0);
                instructions.Add(CilOpCodes.Conv_I);
                break;
            case TypeAnalysisContext type:
                //typeof(T)
                var corLibScope = module.CorLibTypeFactory.CorLibScope;
                var typeFromHandle = corLibScope
                    .CreateTypeReference("System", "Type")
                    .CreateMemberReference("GetTypeFromHandle", MethodSignature.CreateStatic(
                        corLibScope.CreateTypeReference("System", "Type").ToTypeSignature(false),
                        [corLibScope.CreateTypeReference("System", "RuntimeTypeHandle").ToTypeSignature(true)]));

                instructions.Add(CilOpCodes.Ldtoken, type.ToTypeSignature().ToTypeDefOrRef());
                instructions.Add(CilOpCodes.Call, typeFromHandle);
                break;
            default:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic("Unknown operand: " + operand));
                instructions.Add(CilOpCodes.Call, writeLine);
                instructions.Add(CilOpCodes.Ldnull);
                break;
        }
    }

    private static void LoadSwitchSelector(Instruction instruction, MethodAnalysisContext context, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        var selector = instruction.Operands[0];
        var offset = (int)((Immediate)instruction.Operands[1]).Value;
        var size = (int)((Immediate)instruction.Operands[2]).Value;

        if (selector is LocalVariable { Type: { IsValueType: true, IsEnumType: false } type } local
            && TypeSizes.UnboxedSize(type, context.AppContext.Binary.PointerSizeBytes) != size)
        {
            var field = type.Fields.FirstOrDefault(candidate => !candidate.IsStatic
                && candidate.BackingData?.FieldOffset == offset
                && TypeSizes.UnboxedSize(candidate.FieldType, context.AppContext.Binary.PointerSizeBytes) == size);
            if (field != null)
            {
                LoadLocal(local, method, locals);
                method.CilMethodBody!.Instructions.Add(CilOpCodes.Ldfld, field.ToFieldDescriptor());
                return;
            }
        }

        LoadOperand(selector, method, locals, writeLine);
    }
    
    private static bool TryEmitExactTypeComparison(Instruction instruction, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        var left = instruction.Operands[1];
        var right = instruction.Operands[2];

        IOperand typeOperand;
        LocalVariable objLocal;

        if (left is TypeAnalysisContext && IsKlassPointerLoad(right, out var rightLocal))
            (typeOperand, objLocal) = (left, rightLocal);
        else if (right is TypeAnalysisContext && IsKlassPointerLoad(left, out var leftLocal))
            (typeOperand, objLocal) = (right, leftLocal);
        else
            return false;

        var module = method.DeclaringModule!;
        var instructions = method.CilMethodBody!.Instructions;

        var getType = module.CorLibTypeFactory.CorLibScope
            .CreateTypeReference("System", "Object")
            .CreateMemberReference("GetType", MethodSignature.CreateInstance(
                module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "Type").ToTypeSignature(false)));

        LoadLocal(objLocal, method, locals);
        instructions.Add(CilOpCodes.Callvirt, getType);
        LoadOperand(typeOperand, method, locals, writeLine); // emits typeof(T)
        instructions.Add(CilOpCodes.Ceq);

        if (instruction.OpCode == OpCode.CheckNotEqual)
        {
            instructions.Add(CilOpCodes.Ldc_I4_0);
            instructions.Add(CilOpCodes.Ceq);
        }

        StoreToOperand(instruction.Operands[0], method, locals, writeLine);
        return true;
    }
    
    private static bool IsKlassPointerLoad(IOperand operand, out LocalVariable local)
    {
        if (operand is MemoryOperand { Index: null, Addend: 0, Scale: 0, Base: LocalVariable { Type.IsValueType: false } baseLocal })
        {
            local = baseLocal;
            return true;
        }

        local = null!;
        return false;
    }

    private static void PushDefaultOf(TypeAnalysisContext type, CilInstructionCollection instructions)
    {
        //TODO Remove this, we should be handling arguments correctly in ISIL resolution, this is a hack to emit balanced stacks.
        //TODO At the *very* least we should emit a console.writeline saying that we did this.
        if (!type.IsValueType)
        {
            instructions.Add(CilOpCodes.Ldnull);
            return;
        }

        switch (type.FullName)
        {
            case "System.Single": instructions.Add(CilOpCodes.Ldc_R4, 0f); break;
            case "System.Double": instructions.Add(CilOpCodes.Ldc_R8, 0d); break;
            case "System.Int64" or "System.UInt64": instructions.Add(CilOpCodes.Ldc_I8, 0L); break;
            default: instructions.Add(CilOpCodes.Ldc_I4_0); break;
        }
    }

    private static bool IsBoolean(IOperand operand, MethodAnalysisContext context) =>
        operand is LocalVariable { Type: { } type } && type == context.AppContext.SystemTypes.SystemBooleanType;

    private static bool IsZeroConstant(IOperand operand) => operand is Immediate { Value: 0 };
    
    private static TypeAnalysisContext? DestinationType(IOperand destination) =>
        destination switch
        {
            LocalVariable local => local.Type,
            FieldReference field => field.Field.FieldType,
            ArrayAccess { Array.Type: SzArrayTypeAnalysisContext array } => array.ElementType,
            _ => null
        };

    private static void LoadLocal(LocalVariable local, MethodDefinition method, Dictionary<LocalVariable, CilLocalVariable> locals)
    {
        var instructions = method.CilMethodBody!.Instructions;

        if (local.IsThis)
        {
            instructions.Add(CilOpCodes.Ldarg_0);
            return;
        }

        var parameter = method.Parameters.FirstOrDefault(p => p.Name == local.Name);

        if (parameter != null)
            instructions.Add(CilOpCodes.Ldarg, parameter);
        else
            instructions.Add(CilOpCodes.Ldloc, locals[local]);
    }

    private static void StoreToOperand(IOperand operand, MethodDefinition method,
        Dictionary<LocalVariable, CilLocalVariable> locals, IMethodDescriptor writeLine)
    {
        var instructions = method.CilMethodBody!.Instructions;

        switch (operand)
        {
            case LocalVariable local:
                instructions.Add(CilOpCodes.Stloc, locals[local]);
                break;

            case AddressOf { Target: LocalVariable addressed }:
                // Aggregate returns on ARM64 use a caller-provided X8 buffer. The ISIL call keeps
                // that buffer as an AddressOf destination, while the managed IL call returns the
                // value normally and stores it into the corresponding local.
                instructions.Add(CilOpCodes.Stloc, locals[addressed]);
                break;

            case FieldReference field:
                var fieldDescriptor = field.Field.ToFieldDescriptor();

                if (field.Field.IsStatic)
                {
                    instructions.Add(CilOpCodes.Stsfld, fieldDescriptor);
                    break;
                }

                // stfld wants the object underneath the value, but the value is already on the stack, so
                // park it in a temporary while we load the object.
                var scratch = new CilLocalVariable(fieldDescriptor.Signature!.FieldType);
                method.CilMethodBody!.LocalVariables.Add(scratch);

                instructions.Add(CilOpCodes.Stloc, scratch);
                LoadLocal(field.Local, method, locals);
                if (field.ContainingField is { } containing)
                {
                    instructions.Add(CilOpCodes.Ldflda, containing.ToFieldDescriptor());
                    instructions.Add(CilOpCodes.Ldloc, scratch);
                    instructions.Add(CilOpCodes.Stfld, fieldDescriptor);
                }
                else
                {
                    instructions.Add(CilOpCodes.Ldloc, scratch);
                    instructions.Add(CilOpCodes.Stfld, fieldDescriptor);
                }
                break;

            case ArrayAccess arrayAccess:
                // stelem needs array and index before the value, so the same trick as stfld
                var elementType = ((SzArrayTypeAnalysisContext)arrayAccess.Array.Type!).ElementType;
                var elementScratch = new CilLocalVariable(elementType.ToTypeSignature());
                method.CilMethodBody!.LocalVariables.Add(elementScratch);

                instructions.Add(CilOpCodes.Stloc, elementScratch);
                LoadLocal(arrayAccess.Array, method, locals);
                LoadOperand(arrayAccess.Index, method, locals, writeLine);
                instructions.Add(CilOpCodes.Ldloc, elementScratch);
                instructions.Add(CilOpCodes.Stelem, elementType.ToTypeSignature().ToTypeDefOrRef());
                break;

            case MemoryOperand memory:
                if (memory.Index == null && memory.Addend == 0 && memory.Scale == 0
                    && memory.Base is LocalVariable local2)
                {
                    if (local2.Type is ByRefTypeAnalysisContext { ElementType: { IsValueType: true } referent })
                    {
                        // A Move through a byref value type is an indirect aggregate store:
                        // save the value, load the destination address, then emit stobj.
                        var aggregateScratch = new CilLocalVariable(referent.ToTypeSignature());
                        method.CilMethodBody!.LocalVariables.Add(aggregateScratch);
                        instructions.Add(CilOpCodes.Stloc, aggregateScratch);
                        LoadLocal(local2, method, locals);
                        instructions.Add(CilOpCodes.Ldloc, aggregateScratch);
                        instructions.Add(CilOpCodes.Stobj, referent.ToTypeSignature().ToTypeDefOrRef());
                        break;
                    }

                    // Can pointer assignments just be ignored because it's C#? (Move [local], 123)
                    instructions.Add(CilOpCodes.Stloc, locals[local2]);
                    break;
                }
                instructions.Add(CilOpCodes.Pop);
                break;

            default:
                instructions.Add(CilOpCodes.Ldstr, Diagnostic($"Store into unknown operand: {operand}"));
                instructions.Add(CilOpCodes.Call, writeLine);
                instructions.Add(CilOpCodes.Pop);
                break;
        }
    }
}
