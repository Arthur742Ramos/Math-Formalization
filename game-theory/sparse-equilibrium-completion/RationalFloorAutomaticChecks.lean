/- AI-assisted executable regression controls. Apache-2.0. -/
module
public import RationalFloorDecision
public import RationalAllocationChecks
public meta import RationalFloorDecision
public meta import RationalFloorAccuracyParameters
public meta import RationalFloorSearch
public meta import RationalFloorRepertoire
public meta import RationalAllocationChecks
@[expose] public section
open SparseCompletion

def globalThreeQuarterRun := rationalFloorApproximation (initializerTestParameters (3/4))
  (fun _ => 0) (fun _ => by norm_num) 1

theorem globalFloorTestR (a : ℚ) :
    (initializerTestParameters a).R=rationalResidualFloors (fun _ => a) := by
  change RationalLinearSystem.mk
    (fun _ => rationalFormScale (-1) (intervalQForm 1 1 0 0)) (fun _ => -a)=
      RationalLinearSystem.mk (fun i => rationalFormScale (-1) (intervalQForm 1 1 0 i)) (fun _ => -a)
  congr 1
  funext i
  have hi : i=0 := Subsingleton.elim _ _
  rw [hi]

def globalThreeQuarterDecision : Bool := ( rationalFloorClassDecision (initializerTestParameters (3/4))
  (fun _ => 0) (fun _ => 3/4) (fun _ => by norm_num) (fun _ => by norm_num) (globalFloorTestR _) 1 (by norm_num)).decide
def globalImpossibleDecision : Bool := ( rationalFloorClassDecision (initializerTestParameters (5/4))
  (fun _ => 0) (fun _ => 5/4) (fun _ => by norm_num) (fun _ => by norm_num) (globalFloorTestR _) 1 (by norm_num)).decide

#guard globalThreeQuarterRun.isSome
#guard globalThreeQuarterRun.map (fun w => decide (w.1 0 ≤ (1/4 : ℚ)))=some true
#guard globalThreeQuarterDecision
#guard !globalImpossibleDecision
#guard !(rationalFloorApproximation (initializerTestParameters (1/4))
  (fun _ => 0) (fun _ => by norm_num) 0).isSome
#guard !(rationalFloorApproximation initializerEmpty Fin.elim0 (fun i => Fin.elim0 i) 1).isSome

def residualOnlyParameters : RationalIntervalParameters 0 1 (Fin 1) where
  loK := Fin.elim0
  hiK := Fin.elim0
  lo := fun _ => Fin.elim0
  hi := fun _ => Fin.elim0
  p := Fin.elim0
  M := 1
  r := 1
  η := 1/4
  R := rationalResidualFloors (fun _ => 0)
  positiveBound := by norm_num
  positiveSlack := by norm_num
  anchorNonneg := fun a => Fin.elim0 a
  normalized := by norm_num
  coreLower := fun a => Fin.elim0 a
  coreUpper := fun a => Fin.elim0 a
  crossLower := fun _ a => Fin.elim0 a
  crossUpper := fun _ a => Fin.elim0 a
  orderedCross := fun _ a => Fin.elim0 a

def residualOnlyRun := rationalFloorApproximation residualOnlyParameters
  Fin.elim0 (fun a => Fin.elim0 a) 1
#guard residualOnlyRun.isSome
#guard residualOnlyRun.map (fun w => w.2.q 0)=some 1
