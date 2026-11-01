/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.Basic
public meta import LambdaTuring.Basic
public import LambdaTuring.Observation
public meta import LambdaTuring.Observation
public import LambdaTuring.Machine
public meta import LambdaTuring.Machine
public import LambdaTuring.FiniteTable
public meta import LambdaTuring.FiniteTable
public import LambdaTuring.MathlibBridge
public meta import LambdaTuring.MathlibBridge
public import LambdaTuring.SemanticBridge
public meta import LambdaTuring.SemanticBridge
public import LambdaTuring.NumericalSemantics
public meta import LambdaTuring.NumericalSemantics
public import LambdaTuring.Explore
public meta import LambdaTuring.Explore
public import LambdaTuring.ObservationSearch
public meta import LambdaTuring.ObservationSearch
public import LambdaTuring.UnboundedSearch
public meta import LambdaTuring.UnboundedSearch
public import LambdaTuring.TermCode
public meta import LambdaTuring.TermCode
public import LambdaTuring.FoldCode
public meta import LambdaTuring.FoldCode
public import LambdaTuring.DecodeComputable
public meta import LambdaTuring.DecodeComputable
public import LambdaTuring.Destructors
public meta import LambdaTuring.Destructors
public import LambdaTuring.ChurchComputable
public meta import LambdaTuring.ChurchComputable
public import LambdaTuring.SearchComputable
public meta import LambdaTuring.SearchComputable
public import LambdaTuring.BetaStepComputable
public meta import LambdaTuring.BetaStepComputable
public import LambdaTuring.TermSize
public meta import LambdaTuring.TermSize
public import LambdaTuring.LiftTable
public meta import LambdaTuring.LiftTable
public import LambdaTuring.SubstTable
public meta import LambdaTuring.SubstTable
public import LambdaTuring.MachineRun
public meta import LambdaTuring.MachineRun
public import LambdaTuring.MachineSearch
public meta import LambdaTuring.MachineSearch
public import LambdaTuring.MachineCoding
public meta import LambdaTuring.MachineCoding
public import LambdaTuring.MachineExact
public meta import LambdaTuring.MachineExact
public import LambdaTuring.ConstantCompiler
public meta import LambdaTuring.ConstantCompiler
public import LambdaTuring.CPS
public meta import LambdaTuring.CPS
public import LambdaTuring.CPSComposition
public meta import LambdaTuring.CPSComposition
public import LambdaTuring.MachineCompilerBase
public meta import LambdaTuring.MachineCompilerBase
public import LambdaTuring.ChurchSuccessor
public meta import LambdaTuring.ChurchSuccessor
public import LambdaTuring.CPSWithSuccessor
public meta import LambdaTuring.CPSWithSuccessor
public import LambdaTuring.MachineSuccessor
public meta import LambdaTuring.MachineSuccessor
public import LambdaTuring.FragmentBridge
public meta import LambdaTuring.FragmentBridge
public import LambdaTuring.CPSBottom
public meta import LambdaTuring.CPSBottom
public import LambdaTuring.MachineBottom
public meta import LambdaTuring.MachineBottom
public import LambdaTuring.BottomFragmentBridge
public meta import LambdaTuring.BottomFragmentBridge
public import LambdaTuring.CPSWithBottom
public meta import LambdaTuring.CPSWithBottom
public import LambdaTuring.ChurchPairs
public meta import LambdaTuring.ChurchPairs
public import LambdaTuring.ChurchPredecessor
public meta import LambdaTuring.ChurchPredecessor
public import LambdaTuring.CPSPair
public meta import LambdaTuring.CPSPair
public import LambdaTuring.CPSWithPair
public meta import LambdaTuring.CPSWithPair
public import LambdaTuring.PairEnumeration
public meta import LambdaTuring.PairEnumeration
public import LambdaTuring.ChurchUnpair
public meta import LambdaTuring.ChurchUnpair
public import LambdaTuring.CPSProjection
public meta import LambdaTuring.CPSProjection
public import LambdaTuring.CPSWithProjection
public meta import LambdaTuring.CPSWithProjection
public import LambdaTuring.CPSRecursionUnroll
public meta import LambdaTuring.CPSRecursionUnroll
public import LambdaTuring.CPSRecursionState
public meta import LambdaTuring.CPSRecursionState
public import LambdaTuring.CPSRecursion
public meta import LambdaTuring.CPSRecursion
public import LambdaTuring.CPSWithRecursion
public meta import LambdaTuring.CPSWithRecursion
public import LambdaTuring.CPSSearch
public meta import LambdaTuring.CPSSearch
public import LambdaTuring.HeadReduction
public meta import LambdaTuring.HeadReduction
public import LambdaTuring.HeadSearch
public meta import LambdaTuring.HeadSearch
public import LambdaTuring.CPSSearchExact
public meta import LambdaTuring.CPSSearchExact
public import LambdaTuring.HeadSubstitution
public meta import LambdaTuring.HeadSubstitution
public import LambdaTuring.HeadObservable
public meta import LambdaTuring.HeadObservable
public import LambdaTuring.StandardReduction
public meta import LambdaTuring.StandardReduction
public import LambdaTuring.CPSTotalCompiler
public meta import LambdaTuring.CPSTotalCompiler
public import LambdaTuring.ExtensionalCompleteness
public meta import LambdaTuring.ExtensionalCompleteness
public import LambdaTuring.ListCodeBridge
public meta import LambdaTuring.ListCodeBridge
public import LambdaTuring.TM2TM0Bridge
public meta import LambdaTuring.TM2TM0Bridge
public import LambdaTuring.ListCodeTuple
public meta import LambdaTuring.ListCodeTuple
public import LambdaTuring.ListCodeArithmetic
public meta import LambdaTuring.ListCodeArithmetic
public import LambdaTuring.ListCodePairCompiler
public meta import LambdaTuring.ListCodePairCompiler
public import LambdaTuring.ListCodePairTM0
public meta import LambdaTuring.ListCodePairTM0
public import LambdaTuring.ListCodeSqrt
public meta import LambdaTuring.ListCodeSqrt
public import LambdaTuring.ListCodeUnpair
public meta import LambdaTuring.ListCodeUnpair
public import LambdaTuring.ListCodeProjectionCompiler
public meta import LambdaTuring.ListCodeProjectionCompiler
public import LambdaTuring.ListCodePartialRecursion
public meta import LambdaTuring.ListCodePartialRecursion
public import LambdaTuring.ListCodeRecursionCompiler
public meta import LambdaTuring.ListCodeRecursionCompiler
public import LambdaTuring.ListCodeRecursionBridge
public meta import LambdaTuring.ListCodeRecursionBridge
public import LambdaTuring.ListCodeSearch
public meta import LambdaTuring.ListCodeSearch
public import LambdaTuring.ListCodeMinimizationCompiler
public meta import LambdaTuring.ListCodeMinimizationCompiler
public import LambdaTuring.ListCodeTotalCompiler
public meta import LambdaTuring.ListCodeTotalCompiler
public import LambdaTuring.FiniteExtraction
public meta import LambdaTuring.FiniteExtraction
public import LambdaTuring.FiniteSupportList
public meta import LambdaTuring.FiniteSupportList
public import LambdaTuring.FiniteTableExtraction
public meta import LambdaTuring.FiniteTableExtraction
public import LambdaTuring.ThreeSymbolCodec
public meta import LambdaTuring.ThreeSymbolCodec
public import LambdaTuring.ThreeSymbolControl
public meta import LambdaTuring.ThreeSymbolControl
public import LambdaTuring.TM1FiniteTable
public meta import LambdaTuring.TM1FiniteTable
public import LambdaTuring.BlockFiniteTM0
public meta import LambdaTuring.BlockFiniteTM0
public import LambdaTuring.TinyTM1Example
public meta import LambdaTuring.TinyTM1Example
public import LambdaTuring.BlockListDecoder
public meta import LambdaTuring.BlockListDecoder
public import LambdaTuring.BlockTapeDecoder
public meta import LambdaTuring.BlockTapeDecoder
public import LambdaTuring.BlockCodegenProbe
public meta import LambdaTuring.BlockCodegenProbe
public import LambdaTuring.UnaryShift
public meta import LambdaTuring.UnaryShift
public import LambdaTuring.UnaryShiftRepeat
public meta import LambdaTuring.UnaryShiftRepeat
public import LambdaTuring.FixedMoveLeft
public meta import LambdaTuring.FixedMoveLeft
public import LambdaTuring.FixedBlockWriter
public meta import LambdaTuring.FixedBlockWriter
public import LambdaTuring.MachineSequence
public meta import LambdaTuring.MachineSequence
public import LambdaTuring.InsertBlock
public meta import LambdaTuring.InsertBlock
public import LambdaTuring.ConsumeAndInsert
public meta import LambdaTuring.ConsumeAndInsert
public import LambdaTuring.UnaryLoopControl
public meta import LambdaTuring.UnaryLoopControl
public import LambdaTuring.UnaryBlockLoop
public meta import LambdaTuring.UnaryBlockLoop
public import LambdaTuring.UnaryPrefixBlocks
public meta import LambdaTuring.UnaryPrefixBlocks
public import LambdaTuring.ScanBack
public meta import LambdaTuring.ScanBack
public import LambdaTuring.UnaryPreprocessor
public meta import LambdaTuring.UnaryPreprocessor
public import LambdaTuring.UnaryInputEncoding
public meta import LambdaTuring.UnaryInputEncoding
public import LambdaTuring.ListCodeUnaryRecovery
public meta import LambdaTuring.ListCodeUnaryRecovery
public import LambdaTuring.MachineSequenceExact
public meta import LambdaTuring.MachineSequenceExact
public import LambdaTuring.UnaryRecoveryBridge
public meta import LambdaTuring.UnaryRecoveryBridge
public import LambdaTuring.UnarySequenceBridge
public meta import LambdaTuring.UnarySequenceBridge
public import LambdaTuring.ListCodeUnaryOutput
public meta import LambdaTuring.ListCodeUnaryOutput
public import LambdaTuring.UnaryOutputShapeBridge
public meta import LambdaTuring.UnaryOutputShapeBridge
public import LambdaTuring.ClearEncodedBlock
public meta import LambdaTuring.ClearEncodedBlock
public import LambdaTuring.OutputGapless
public meta import LambdaTuring.OutputGapless
public import LambdaTuring.ClearBlockLoop
public meta import LambdaTuring.ClearBlockLoop
public import LambdaTuring.ClearBlockMachine
public meta import LambdaTuring.ClearBlockMachine
public import LambdaTuring.ClearBlockSide
public meta import LambdaTuring.ClearBlockSide
public import LambdaTuring.MainTrackReader
public meta import LambdaTuring.MainTrackReader
public import LambdaTuring.MainTrackMachine
public meta import LambdaTuring.MainTrackMachine
public import LambdaTuring.OutputAppend
public meta import LambdaTuring.OutputAppend
public import LambdaTuring.OutputFinish
public meta import LambdaTuring.OutputFinish
public import LambdaTuring.OutputQuotient
public meta import LambdaTuring.OutputQuotient
public import LambdaTuring.OutputMarkBlock
public meta import LambdaTuring.OutputMarkBlock
public import LambdaTuring.OutputAppendBridge
public meta import LambdaTuring.OutputAppendBridge
public import LambdaTuring.ReaderFiniteControl
public meta import LambdaTuring.ReaderFiniteControl
public import LambdaTuring.OutputReadAppend
public meta import LambdaTuring.OutputReadAppend
public import LambdaTuring.OutputSafeAppend
public meta import LambdaTuring.OutputSafeAppend
public import LambdaTuring.OutputSafeBridge
public meta import LambdaTuring.OutputSafeBridge
public import LambdaTuring.OutputDispatch
public meta import LambdaTuring.OutputDispatch
public import LambdaTuring.OutputValueLoop
public meta import LambdaTuring.OutputValueLoop
public import LambdaTuring.OutputRepeat
public meta import LambdaTuring.OutputRepeat
public import LambdaTuring.OutputInitialize
public meta import LambdaTuring.OutputInitialize
public import LambdaTuring.OutputEndToEnd
public meta import LambdaTuring.OutputEndToEnd
public import LambdaTuring.ExtensionalMachine
public meta import LambdaTuring.ExtensionalMachine
public import LambdaTuring.ExecutableTermCoding
public meta import LambdaTuring.ExecutableTermCoding
public import LambdaTuring.UniformLambdaEval
public meta import LambdaTuring.UniformLambdaEval
public import LambdaTuring.UniformMachineSyntax
public meta import LambdaTuring.UniformMachineSyntax
public import LambdaTuring.UnaryCodegenAudit
public meta import LambdaTuring.UnaryCodegenAudit
public import LambdaTuring.EffectiveCode
public meta import LambdaTuring.EffectiveCode
public import LambdaTuring.ProofReifier
public meta import LambdaTuring.ProofReifier
public import LambdaTuring.EncodedTapeAction
public meta import LambdaTuring.EncodedTapeAction
public import LambdaTuring.EncodedMachineStep
public meta import LambdaTuring.EncodedMachineStep
public import LambdaTuring.EncodedMachineRun
public meta import LambdaTuring.EncodedMachineRun
public import LambdaTuring.EncodedMachineEvaluator
public meta import LambdaTuring.EncodedMachineEvaluator
public import LambdaTuring.DirectCourseCode
public meta import LambdaTuring.DirectCourseCode
public import LambdaTuring.DirectBetaPath
public meta import LambdaTuring.DirectBetaPath
public import LambdaTuring.DirectBetaCode
public meta import LambdaTuring.DirectBetaCode
public import LambdaTuring.DirectBetaTraceCode
public meta import LambdaTuring.DirectBetaTraceCode
public import LambdaTuring.DirectLambdaToMachine
public meta import LambdaTuring.DirectLambdaToMachine
public import LambdaTuring.NumeralReduction
public meta import LambdaTuring.NumeralReduction
public import LambdaTuring.LambdaRice
public meta import LambdaTuring.LambdaRice
public import LambdaTuring.LambdaTotality
public meta import LambdaTuring.LambdaTotality

@[expose] public section
