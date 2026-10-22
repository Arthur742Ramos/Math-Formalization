/- AI-assisted executable source-payoff controls. Apache-2.0. -/
module
public import RationalBinnedResponse
public import RationalExplicitBinPayoffChecks
public meta import RationalBinnedWeights
public meta import RationalBinnedOmitted
public meta import RationalExplicitBinPayoffChecks
public meta import RationalExplicitBinPayoff
public meta import Mathlib.Algebra.BigOperators.Fin
@[expose] public section
open SparseCompletion
open scoped BigOperators

theorem explicitBinTestPositive (b : Fin 2) : 0 < explicitBinTestLengths b := by
  unfold explicitBinTestLengths
  split_ifs <;> norm_num

def explicitBinTestWeights := rationalBinnedWeights explicitBinTestLengths explicitBinTestPositive (1/4)

#guard (∑ i,explicitBinTestWeights i)=1/4
#guard ∀ i, 0 ≤ explicitBinTestWeights i
#guard explicitBinTestWeights (explicitBinTestIndex 0)=0
#guard explicitBinTestWeights (explicitBinTestIndex 1)=1/10
#guard explicitBinTestWeights (explicitBinTestIndex 2)=1/10
#guard explicitBinTestWeights (explicitBinTestIndex 3)=0
#guard explicitBinTestWeights (explicitBinTestIndex 4)=1/20
#guard ∀ i, rationalUniformScore (1/4) i+
  (∑ j,rationalExplicitBinPayoff explicitBinTestLengths i j*explicitBinTestWeights j)=0
#guard ∀ i, rationalBinnedWeights explicitBinTestLengths explicitBinTestPositive 0 i=0
#guard ∀ i j, -1 ≤ rationalExplicitBinPayoff explicitBinTestLengths i j ∧
  rationalExplicitBinPayoff explicitBinTestLengths i j ≤ 1
#guard ∀ i j, rationalExplicitBinPayoff explicitBinTestLengths i j=
  -rationalExplicitBinPayoff explicitBinTestLengths j i
