/- AI-assisted executable source-payoff controls. Apache-2.0. -/
module
public import RationalExplicitBinPayoff
public meta import RationalExplicitBinPayoff
public meta import Mathlib.Algebra.BigOperators.Fin
@[expose] public section
open SparseCompletion
open scoped BigOperators

def explicitBinTestLengths : Fin 2 → ℕ := fun b => if b.val=0 then 4 else 1

theorem explicitBinTestTotal : (∑ b,explicitBinTestLengths b)=5 := by
  simp [Fin.sum_univ_two,explicitBinTestLengths]

def explicitBinTestIndex (i : Fin 5) : Fin (∑ b,explicitBinTestLengths b) :=
  ⟨i.val,by rw [explicitBinTestTotal]; exact i.isLt⟩

#guard rationalBinRepresentative explicitBinTestLengths (explicitBinTestIndex 0)=false
#guard rationalBinRepresentative explicitBinTestLengths (explicitBinTestIndex 1)=true
#guard rationalBinRepresentative explicitBinTestLengths (explicitBinTestIndex 2)=true
#guard rationalBinRepresentative explicitBinTestLengths (explicitBinTestIndex 4)=true
#guard rationalExplicitBinPayoff explicitBinTestLengths (explicitBinTestIndex 1) (explicitBinTestIndex 2)= -1/2
#guard rationalExplicitBinPayoff explicitBinTestLengths (explicitBinTestIndex 2) (explicitBinTestIndex 1)=1/2
#guard rationalExplicitBinPayoff explicitBinTestLengths (explicitBinTestIndex 1) (explicitBinTestIndex 4)= -1
#guard rationalExplicitBinPayoff explicitBinTestLengths (explicitBinTestIndex 4) (explicitBinTestIndex 1)=1
#guard rationalExplicitBinPayoff explicitBinTestLengths (explicitBinTestIndex 0) (explicitBinTestIndex 1)= -4/5
#guard rationalExplicitBinPayoff explicitBinTestLengths (explicitBinTestIndex 1) (explicitBinTestIndex 0)=4/5
#guard rationalExplicitBinPayoff explicitBinTestLengths (explicitBinTestIndex 4) (explicitBinTestIndex 4)=0
