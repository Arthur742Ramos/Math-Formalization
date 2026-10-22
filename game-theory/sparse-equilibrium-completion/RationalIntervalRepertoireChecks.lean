/- AI-assisted executable regression controls. Apache-2.0. -/
module
public import RationalIntervalAccurate
public meta import RationalIntervalAccurate
public meta import RationalIntervalSearch
public meta import RationalIntervalRepertoireSolver
public meta import RationalIntervalRepertoire
public meta import RationalIntervalPhysical
public meta import RationalIntervalPack
public meta import RationalIntervalEncoding
public meta import RationalIntervalForms
public meta import RationalIntervalVariables
public meta import RationalLinearForms
public meta import RationalIntervalRecovery
public meta import RationalResidualGap
public meta import RationalResidualSolver
public meta import RationalLinearSolver
public meta import RationalOneVariableFintype
public meta import RationalGrid
public meta import RationalLogRounds
public meta import Bisection
@[expose] public section
open SparseCompletion

def intervalTestNoRepertoire : RationalLinearSystem (Fin 0) (1+(1*1+(1*1+0*1))) :=
  ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩

def intervalTestModel : RationalIntervalModel 1 1 (Fin 0) where
  loK := fun _ _ => 0
  hiK := fun _ _ => 0
  lo := fun _ _ => 0
  hi := fun _ _ => 0
  p := fun _ => 1/2
  M := 1
  r := 1/2
  η := 1/4
  R := intervalTestNoRepertoire
  positiveBound := by norm_num
  positiveSlack := by norm_num
  anchorNonneg := fun _ => by norm_num
  normalized := by norm_num
  coreLower := fun _ _ => by norm_num
  coreUpper := fun _ _ => by norm_num
  crossLower := fun _ _ => by norm_num
  crossUpper := fun _ _ => by norm_num
  orderedCross := fun _ _ => by norm_num
  compatibleNonempty := by
    refine ⟨fun _ => 1/2,fun _ _ => 0,fun _ _ => 0,fun _ _ => 0,?_⟩
    norm_num [IsSkew,RationalLinearSystem.RealSatisfies,intervalTestNoRepertoire]

def intervalTestFloor (a : ℚ) : RationalLinearSystem (Fin 1) (1+(1*1+(1*1+0*1))) :=
  ⟨fun _ => rationalFormScale (-1) (intervalQForm 1 1 0 0),fun _ => -a⟩

#guard (rationalIntervalRepertoireAlgorithm (k := 1) (m := 1)
  (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
  (fun _ => 1/2) 1 (1/2) 0 (1/4) (intervalTestFloor (1/4))).isSome
#guard !(rationalIntervalRepertoireAlgorithm (k := 1) (m := 1)
  (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
  (fun _ => 1/2) 1 (1/2) 0 (1/4) (intervalTestFloor (3/4))).isSome
#guard (rationalIntervalAccurateApproximation intervalTestModel (1/8)).isSome
#guard (rationalIntervalAccurateApproximation intervalTestModel (1/8)).map
  (fun w => decide (w.1.2-w.1.1 < (1/8 : ℚ)))=some true
#guard !(rationalIntervalRepertoireAlgorithm (k := 1) (m := 1)
  (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
  (fun _ => 1/2) 1 (1/2) (-1) (1/4) intervalTestNoRepertoire).isSome
