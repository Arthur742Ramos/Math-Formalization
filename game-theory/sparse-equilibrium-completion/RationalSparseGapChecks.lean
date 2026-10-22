/- Executable controls for the sparse gap search. AI-assisted, Apache-2.0. -/
module
public import RationalSparseGapAlgorithm
public meta import RationalSparseGapAlgorithm
public meta import RationalSparseGapSearch
public meta import RationalSparseSupport
public meta import RationalAllocationGrid
public meta import RationalFiniteSelection
public meta import RationalGapDecision
public meta import RationalGapEncoding
public meta import RationalGap
public meta import RationalGrid
public meta import RationalResidualGap
public meta import RationalResidualSolver
public meta import RationalLinearSolver
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def sparseGapNoRows (m : ℕ) : RationalLinearSystem (Fin 0) m :=
  ⟨Fin.elim0,Fin.elim0⟩

def sparseGapFour := rationalSparseGapAlgorithm (k := 0) (m := 4)
  Fin.elim0 (fun _ => Fin.elim0) Fin.elim0 1 1 1 1 (sparseGapNoRows 4)

#guard sparseGapFour.isSome
#guard sparseGapFour.all (fun w => (Finset.univ.filter (fun i => w.1 i ≠ 0)).card ≤ 3)
#guard sparseGapFour.all (fun w => (∑ i, w.1 i)=1)
#guard sparseGapFour.all (fun w => ∀ i, 0 ≤ w.1 i)
#guard sparseGapFour.all (fun w => decide (∀ i j, w.2 i j= -w.2 j i))
#guard sparseGapFour.all (fun w => decide (∀ i j, -1 ≤ w.2 i j ∧ w.2 i j ≤ 1))
#guard sparseGapFour.all (fun w => decide (∀ i, ∑ j, w.2 i j*w.1 j ≤ 2))
#guard (rationalSparseGapAlgorithm (k := 0) (m := 0) Fin.elim0 Fin.elim0 Fin.elim0
  1 0 0 1 (sparseGapNoRows 0)).isSome
#guard (rationalSparseGapAlgorithm (k := 0) (m := 0) Fin.elim0 Fin.elim0 Fin.elim0
  1 1 0 1 (sparseGapNoRows 0)).isNone

end SparseCompletion
