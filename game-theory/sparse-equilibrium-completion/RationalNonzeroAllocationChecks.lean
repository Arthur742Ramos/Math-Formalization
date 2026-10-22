/- AI-assisted executable regression controls. Apache-2.0. -/
module
public import RationalAllocationChecks
public import RationalFloorRepertoire
public meta import RationalAllocationChecks
public meta import RationalFloorRepertoire
public meta import RationalAllocationRun
public meta import RationalAllocationGrid
public meta import RationalFiniteSelection
@[expose] public section
open SparseCompletion

def noResidualTwoCore (a b : Fin 2) : ℚ :=
  if a.val=0 then (if b.val=0 then 0 else -1) else (if b.val=0 then 1 else 0)
def noResidualTwoFloor (a : Fin 2) : ℚ := if a.val=0 then 1/4 else 0

def noResidualTwoParameters : RationalIntervalParameters 2 0 (Fin 0) where
  loK := noResidualTwoCore
  hiK := noResidualTwoCore
  lo := Fin.elim0
  hi := Fin.elim0
  p := fun _ => 1/2
  M := 1
  r := 0
  η := 1/8
  R := rationalResidualFloors Fin.elim0
  positiveBound := by norm_num
  positiveSlack := by norm_num
  anchorNonneg := fun _ => by norm_num
  normalized := by norm_num [Fin.sum_univ_succ]
  coreLower := fun a b => by dsimp only [noResidualTwoCore]; split_ifs <;> norm_num
  coreUpper := fun a b => by dsimp only [noResidualTwoCore]; split_ifs <;> norm_num
  crossLower := fun i => Fin.elim0 i
  crossUpper := fun i => Fin.elim0 i
  orderedCross := fun i => Fin.elim0 i

def noResidualTwoRun := rationalReservoirSearch noResidualTwoParameters noResidualTwoFloor
  (fun a => by dsimp only [noResidualTwoFloor]; split_ifs <;> norm_num) (1/4) (1/16) 0

#guard noResidualTwoRun.isSome
#guard noResidualTwoRun.map (fun w => w.1 0)=some (1/4)
#guard noResidualTwoRun.map (fun w => w.1 1)=some (3/4)
#guard noResidualTwoRun.map (fun w => w.2.bracket.2)=some (1/4)
#guard noResidualTwoRun.map (fun w => w.2.K 0 1)=some (-1)
#guard noResidualTwoRun.map (fun w => w.2.K 1 0)=some 1
