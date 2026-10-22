/- AI-assisted executable regression controls. Apache-2.0. -/
module
public import RationalFloorSparseDecision
public import RationalFloorAutomaticChecks
public meta import RationalFloorSparseDecision
public meta import RationalFloorSparseValue
public meta import RationalFloorSparsify
public meta import RationalFloorAutomaticChecks
public meta import RationalAllocationChecks
public meta import RationalIntervalInitializerChecks
@[expose] public section
open SparseCompletion

def sparseGlobalZeroRun := rationalFloorSparseApproximation (initializerTestParameters 0)
  (fun _ => 0) (fun _ => by norm_num) 1

def sparseGlobalZeroDecision : Bool := (rationalSparseFloorClassDecision (initializerTestParameters 0)
  (fun _ => 0) (fun _ => by norm_num) (globalFloorTestR 0) 1 (by norm_num)).decide

def sparseGlobalImpossibleDecision : Bool := (rationalSparseFloorClassDecision (initializerTestParameters 0)
  (fun _ => 2) (fun _ => by norm_num) (globalFloorTestR 0) 1 (by norm_num)).decide

#guard sparseGlobalZeroRun.isSome
#guard sparseGlobalZeroDecision
#guard !sparseGlobalImpossibleDecision
#guard sparseGlobalZeroRun.map (fun v => decide (v.1 0+v.2.q 0=1))=some true
#guard sparseGlobalZeroRun.map (fun v => v.2.B 0 0)=some 0
#guard sparseGlobalZeroRun.map (fun v => v.2.K 0 0)=some 0
#guard sparseGlobalZeroRun.map (fun v => v.2.D 0 0)=some 0
#guard sparseGlobalZeroRun.map (fun v => decide (0 ≤ v.2.bracket.2 ∧ v.2.bracket.2 < 1))=some true
#guard !(rationalFloorSparseApproximation (initializerTestParameters 0)
  (fun _ => 0) (fun _ => by norm_num) 0).isSome
#guard !(rationalFloorSparseApproximation initializerEmpty Fin.elim0 (fun i => Fin.elim0 i) 1).isSome

def sparseGlobalResidualOnly := rationalFloorSparseApproximation residualOnlyParameters
  Fin.elim0 (fun a => Fin.elim0 a) 1
#guard sparseGlobalResidualOnly.isSome
#guard sparseGlobalResidualOnly.map (fun v => v.2.q 0)=some 1

def sparseGlobalNoResidual := rationalFloorSparseApproximation initializerNoResidual
  (fun _ => 0) (fun _ => by norm_num) 1
#guard sparseGlobalNoResidual.isSome
#guard sparseGlobalNoResidual.map (fun v => v.1 0)=some 1
