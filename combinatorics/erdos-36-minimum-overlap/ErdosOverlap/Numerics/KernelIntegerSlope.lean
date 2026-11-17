/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.KernelLeafDecision

@[expose] public section
namespace ErdosOverlap.FrontierLeaves
open Numerics

/-- Exact integer cross multiplication for the physical slope denominator. -/
def slopeRatioEq (q : ℚ) (n : ℤ) : Prop :=
  q.num * 1000000000000000000 = n * (q.den : ℤ)

instance (q : ℚ) (n : ℤ) : Decidable (slopeRatioEq q n) :=
  inferInstanceAs (Decidable (q.num * 1000000000000000000 = n * (q.den : ℤ)))

theorem slopeRatioEq_iff (q : ℚ) (n : ℤ) :
    q = (n : ℚ)/1000000000000000000 ↔ slopeRatioEq q n := by
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hD : (1000000000000000000 : ℚ) ≠ 0 := by norm_num
  have hq : (q.num : ℚ)/(q.den : ℚ) = q := q.num_div_den
  constructor
  · intro h
    have hc : (q.num : ℚ)*1000000000000000000 = (n : ℚ)*(q.den : ℚ) :=
      (div_eq_div_iff hd hD).mp (hq.trans h)
    change q.num * 1000000000000000000 = n * (q.den : ℤ)
    exact_mod_cast hc
  · intro h
    change q.num * 1000000000000000000 = n * (q.den : ℤ) at h
    exact hq.symm.trans ((div_eq_div_iff hd hD).mpr (by exact_mod_cast h))

/-- Every original endpoint and cell-count condition is retained. Only the
test of rational equality uses its proved integer equivalent. -/
def slopeIntegerCheck (mode : Fin 20) (tauNumerator : ℤ)
    (cell : Option ℕ) (l r lam : ℚ) : Bool :=
  match cell with
  | none => decide (r ≤ (FrontierWitnesses.modeFirstCell mode : ℚ)/16384 ∧
      slopeRatioEq lam (2*tauNumerator))
  | some j => decide (j < FrontierWitnesses.modeTailCells mode ∧
      ((FrontierWitnesses.modeFirstCell mode+j : ℕ) : ℚ)/16384 ≤ l ∧
      r ≤ ((((FrontierWitnesses.modeFirstCell mode+j : ℕ) : ℚ)+1)/16384) ∧
      slopeRatioEq lam ((FrontierWitnesses.modeSlopeCache mode).numerators.getD j 0))

theorem slopeIntegerCheck_eq (mode : Fin 20) (tauNumerator : ℤ)
    (tau : FrontierWitnesses.modeTau mode = (tauNumerator : ℚ)/1000000000000000000)
    (cell : Option ℕ) (l r lam : ℚ) :
    slopeIntegerCheck mode tauNumerator cell l r lam =
      FrontierWitnesses.slopeLeafCheck mode cell l r lam := by
  have twice : 2*FrontierWitnesses.modeTau mode =
      ((2*tauNumerator : ℤ) : ℚ)/1000000000000000000 := by
    rw [tau]
    push_cast
    ring
  cases cell with
  | none =>
    simp only [slopeIntegerCheck, FrontierWitnesses.slopeLeafCheck,
      ← slopeRatioEq_iff, ← twice]
  | some j =>
    simp only [slopeIntegerCheck, FrontierWitnesses.slopeLeafCheck,
      FrontierWitnesses.cachedLambda, PLSlopeCache.value, Nat.cast_ofNat,
      ← slopeRatioEq_iff]
    rfl

def profileIntegerCheck (mode : Fin 20) (tauNumerator : ℤ) (leaf : ProfileLeaf) : Bool :=
  let g := leaf.geometry.val
  capacityCheck g.left g.right &&
  slopeIntegerCheck mode tauNumerator leaf.cell g.left g.right leaf.lam &&
  decide (leaf.lower ≤
    ((profileWeights g leaf.lam).integralBox g.cache.integrals g.left g.right).lo)

theorem profileIntegerCheck_eq (mode : Fin 20) (tauNumerator : ℤ)
    (tau : FrontierWitnesses.modeTau mode = (tauNumerator : ℚ)/1000000000000000000)
    (leaf : ProfileLeaf) : profileIntegerCheck mode tauNumerator leaf = leaf.check mode := by
  simp only [profileIntegerCheck, ProfileLeaf.check, slopeIntegerCheck_eq mode tauNumerator tau]

theorem all_profile_check_of_integer {mode : Fin 20} {tauNumerator : ℤ}
    (tau : FrontierWitnesses.modeTau mode = (tauNumerator : ℚ)/1000000000000000000)
    {leaves : List ProfileLeaf}
    (checked : leaves.all (fun leaf => profileIntegerCheck mode tauNumerator leaf) = true) :
    leaves.all (fun leaf => leaf.check mode) = true := by
  simpa only [profileIntegerCheck_eq mode tauNumerator tau] using checked

macro "erdos_profile_integer_decide " tau:term : tactic =>
  `(tactic| (
    apply all_profile_check_of_integer $tau
    erdos_leaves_decide
  ))

end ErdosOverlap.FrontierLeaves
