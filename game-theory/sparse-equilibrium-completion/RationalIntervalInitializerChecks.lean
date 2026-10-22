/- AI-assisted executable regression controls. Apache-2.0. -/
module
public import RationalIntervalInitializedSoundness
public import RationalIntervalRepertoireChecks
public meta import RationalIntervalInitializedAlgorithm
public meta import RationalIntervalInitialize
public meta import RationalIntervalConsistency
public meta import RationalIntervalRepertoireChecks
@[expose] public section
open SparseCompletion

def initializerTestParameters (floor : ℚ) : RationalIntervalParameters 1 1 (Fin 1) where
  loK := fun _ _ => 0
  hiK := fun _ _ => 0
  lo := fun _ _ => 0
  hi := fun _ _ => 0
  p := fun _ => 1/2
  M := 1
  r := 1/2
  η := 1/4
  R := intervalTestFloor floor
  positiveBound := by norm_num
  positiveSlack := by norm_num
  anchorNonneg := fun _ => by norm_num
  normalized := by norm_num
  coreLower := fun _ _ => by norm_num
  coreUpper := fun _ _ => by norm_num
  crossLower := fun _ _ => by norm_num
  crossUpper := fun _ _ => by norm_num
  orderedCross := fun _ _ => by norm_num

#guard decide (initializerTestParameters (1/4)).Compatible
#guard !(decide (initializerTestParameters (3/4)).Compatible)
#guard (rationalIntervalInitialize (initializerTestParameters (1/4))).isSome
#guard !(rationalIntervalInitialize (initializerTestParameters (3/4))).isSome
#guard (rationalIntervalInitializedApproximation (initializerTestParameters (1/4)) (1/8)).isSome
#guard !(rationalIntervalInitializedApproximation (initializerTestParameters (3/4)) (1/8)).isSome
#guard (rationalIntervalInitializedApproximation (initializerTestParameters (1/4)) (1/8)).map
  (fun o => decide (o.bracket.2-o.bracket.1 < (1/8 : ℚ)))=some true

def initializerNoResidual : RationalIntervalParameters 1 0 (Fin 0) where
  loK := fun _ _ => 0
  hiK := fun _ _ => 0
  lo := Fin.elim0
  hi := Fin.elim0
  p := fun _ => 1
  M := 1
  r := 0
  η := 1/4
  R := ⟨Fin.elim0,Fin.elim0⟩
  positiveBound := by norm_num
  positiveSlack := by norm_num
  anchorNonneg := fun _ => by norm_num
  normalized := by norm_num
  coreLower := fun _ _ => by norm_num
  coreUpper := fun _ _ => by norm_num
  crossLower := fun i => Fin.elim0 i
  crossUpper := fun i => Fin.elim0 i
  orderedCross := fun i => Fin.elim0 i

#guard decide initializerNoResidual.Compatible
#guard (rationalIntervalInitializedApproximation initializerNoResidual (1/8)).isSome

def initializerEmpty : RationalIntervalParameters 0 0 (Fin 0) where
  loK := Fin.elim0
  hiK := Fin.elim0
  lo := Fin.elim0
  hi := Fin.elim0
  p := Fin.elim0
  M := 1
  r := 1
  η := 1/4
  R := ⟨Fin.elim0,Fin.elim0⟩
  positiveBound := by norm_num
  positiveSlack := by norm_num
  anchorNonneg := fun i => Fin.elim0 i
  normalized := by norm_num
  coreLower := fun i => Fin.elim0 i
  coreUpper := fun i => Fin.elim0 i
  crossLower := fun i => Fin.elim0 i
  crossUpper := fun i => Fin.elim0 i
  orderedCross := fun i => Fin.elim0 i

#guard !(decide initializerEmpty.Compatible)
#guard !(rationalIntervalInitializedApproximation initializerEmpty (1/8)).isSome
