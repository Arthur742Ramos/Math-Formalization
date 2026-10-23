/- AI-assisted exact rational controls for the mathematical construction only. -/
module
public import Example243
public meta import Example243
public meta import RationalBinnedOmitted
public meta import Mathlib.Algebra.BigOperators.Fin
@[expose] public section
open SparseCompletion
open scoped BigOperators

#guard (∑ b, example243Lengths b)=243
#guard example243ErrorQ=91/1417176
#guard example243CoreChangeQ=91/531441
#guard example243CoreChangeQ < (1/5000 : ℚ)
#guard (Finset.univ.filter fun v => example243FullWeightsQ v ≠ 0).card=11
#guard (∑ v, example243FullWeightsQ v)=1

private def j0 : Fin (∑ b, example243Lengths b) := ⟨0, by decide⟩
private def j13 : Fin (∑ b, example243Lengths b) := ⟨13, by decide⟩
private def j40 : Fin (∑ b, example243Lengths b) := ⟨40, by decide⟩
#guard example243WeightsQ j0=0
#guard example243WeightsQ j13=1/36
#guard example243PayoffQ j13 j40= -1
#guard example243PayoffQ j0 j13= -242/243
#guard rationalUniformScore (1/4) j0+
  (∑ j, example243PayoffQ j0 j*example243WeightsQ j)=0
