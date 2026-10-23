module
public import RationalCoveredGaussianWitness
public meta import RationalCoveredGaussianWitness
public import Mathlib.Data.Finset.Insert
public meta import Mathlib.Data.Finset.Insert
/- Source-only asserted controls; unexecuted until a new root grant. -/
open SparseCompletion
def testCover : Finset (Fin 7) := {1, 4, 6}
def testCoverTable := coverIndexTable testCover
#guard testCoverTable.anchors.toList.map Fin.val == [1, 4, 6]
#guard testCoverTable.residuals.toList.map Fin.val == [0, 2, 3, 5]
#guard (coverTableEncode testCoverTable (4 : Fin 7)) == Sum.inl ⟨1, by decide⟩
#guard (coverTableEncode testCoverTable (3 : Fin 7)) == Sum.inr ⟨2, by decide⟩
#guard (List.finRange 7).all (fun v => coverTableDecode testCoverTable
  (coverTableEncode testCoverTable v) == v)
def testObservation (i j : Fin 7) : ℚ := 10*i.val+j.val
#guard coverDecodeMatrix testCover (coverEncodeMatrix testCover testObservation) 6 2 == 62
#guard (coverIndexTable (∅ : Finset (Fin 4))).residuals.toList.map Fin.val == [0, 1, 2, 3]
#guard (coverIndexTable (Finset.univ : Finset (Fin 4))).anchors.toList.map Fin.val == [0, 1, 2, 3]
/- Source-only asserted whole-program controls; no evaluator run yet. -/
open SparseCompletion
open scoped BigOperators
def suppliedCover : Finset (Fin 3) := {1}
def suppliedWeights (v : Fin 3) : ℚ := if v=1 then 1/2 else 1/4
def suppliedPayoff (u v : Fin 3) : ℚ :=
  if u=v then 0 else if u=0 then (if v=1 then 1/2 else -1)
  else if u=1 then (if v=0 then -1/2 else 1/2)
  else if v=0 then 1 else -1/2
def noExtra : Fin 0 → Fin 3 → ℚ := Fin.elim0
def suppliedGeneral := rationalCoveredGaussianGeneral suppliedCover suppliedPayoff noExtra suppliedWeights 1 0 (1/16)
def suppliedExact := rationalCoveredGaussianExact suppliedCover suppliedPayoff noExtra suppliedWeights 1 (1/16)
#guard (List.finRange 3).all (fun v => suppliedGeneral.1.get v == suppliedWeights v)
#guard (List.finRange 3).all (fun v => suppliedExact.1.get v == suppliedWeights v)
#guard Gaussian.entry suppliedExact.2 0 2 == -3/4
#guard Gaussian.entry suppliedExact.2 2 0 == 3/4
#guard Gaussian.entry suppliedExact.2 0 1 == suppliedPayoff 0 1
#guard Gaussian.entry suppliedExact.2 1 2 == suppliedPayoff 1 2
def zeroResidualWeights (v : Fin 3) : ℚ := if v=1 then 1 else 0
def suppliedZero := rationalCoveredGaussianExact suppliedCover (fun _ _ => 0) noExtra zeroResidualWeights 1 (1/16)
#guard (List.finRange 3).all (fun v => suppliedZero.1.get v == zeroResidualWeights v)
#guard (List.finRange 3).all (fun u => (List.finRange 3).all (fun v => Gaussian.entry suppliedZero.2 u v == 0))
def emptyCoverRun := rationalCoveredGaussianGeneral (∅ : Finset (Fin 4))
  (fun _ _ => 0) (Fin.elim0 : Fin 0 → Fin 4 → ℚ) (fun _ => 1/4) 1 0 (1/4)
#guard (rationalWeightSupport emptyCoverRun.1.get).card ≤ 3
