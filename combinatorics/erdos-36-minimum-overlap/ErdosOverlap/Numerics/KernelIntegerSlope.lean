/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.KernelLeafDecision
public import ErdosOverlap.Numerics.FixedBoxFast

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

end ErdosOverlap.FrontierLeaves

namespace ErdosOverlap.Numerics
@[expose] public section

def FixedBox.mulRatSkippingZero (q : ℚ) (interval : FixedBox) : FixedBox :=
  if q = 0 then ⟨0, 0⟩ else (FixedBox.ofRat q).mulFast interval

theorem FixedBox.mulRatSkippingZero_eq (q : ℚ) (interval : FixedBox) :
    FixedBox.mulRatSkippingZero q interval = (FixedBox.ofRat q).mul interval := by
  by_cases h : q = 0
  · subst q
    have floorZero : (0 : ℚ).floor = 0 := by decide +kernel
    simp [FixedBox.mulRatSkippingZero, FixedBox.ofRat, floorZero, FixedBox.mul, FixedBox.minProduct,
      FixedBox.maxProduct]
  · simp only [FixedBox.mulRatSkippingZero, ite_eq_right h, FixedBox.mulFast_eq_mul]

def LeafWeights.integralBoxSparse (w : LeafWeights) (I : LeafIntegralBoxes) (lo hi : ℚ) : FixedBox :=
  let term := FixedBox.mulRatSkippingZero
  ((((term w.weightA.constant I.integralA).add (term w.weightA.slope I.momentA)).add
    (term w.weightB.constant I.integralB)).add (term w.weightB.slope I.momentB)).add
    ((term w.weight0.constant (FixedBox.ofRat (hi - lo))).add
      (term w.weight0.slope (FixedBox.ofRat ((hi ^ 2 - lo ^ 2) / 2))))

theorem LeafWeights.integralBoxSparse_eq (w : LeafWeights) (I : LeafIntegralBoxes) (lo hi : ℚ) :
    w.integralBoxSparse I lo hi = w.integralBox I lo hi := by
  simp only [integralBoxSparse, integralBox, FixedBox.mulRatSkippingZero_eq]

private theorem FixedBox.positiveLine_eq_zero_of_upper_nonpos (I : FixedBox) (h : I.hi ≤ 0) :
    I.positiveLine = ⟨0, 0⟩ := by
  have upperNonpos : (I.hi : ℚ) / (fixedScale : ℚ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h) (by exact_mod_cast fixedScale_pos.le)
  unfold FixedBox.positiveLine ErdosOverlap.Numerics.positiveLine
  have nonpos : I.upperRat ≤ 0 := upperNonpos
  exact ite_eq_left nonpos

theorem conjugateWeights_eq_zero_of_gates (IA IB : FixedBox) (lam : ℚ) (L K V : RationalAffine)
    (first : (firstGateBox IA IB lam).hi ≤ 0)
    (second : (secondGateBox IA IB lam).hi ≤ 0)
    (selector : boxPositiveSelector IB = 0) :
    conjugateWeights IA IB lam L K V = ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩ := by
  simp [conjugateWeights, FixedBox.positiveLine_eq_zero_of_upper_nonpos _ first,
    FixedBox.positiveLine_eq_zero_of_upper_nonpos _ second, selector, RationalAffine.scale,
    RationalAffine.add, RationalAffine.sub]

end
end ErdosOverlap.Numerics

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section

def profileIntegralBoxSparse (g : Geometry) (lam : ℚ) : FixedBox :=
  let a := g.cache.rangeA
  let b := g.cache.rangeB
  if (firstGateBox a b lam).hi ≤ 0 ∧ (secondGateBox a b lam).hi ≤ 0 ∧ boxPositiveSelector b = 0 then
    ⟨0, 0⟩
  else (profileWeights g lam).integralBoxSparse g.cache.integrals g.left g.right

theorem profileIntegralBoxSparse_eq (g : Geometry) (lam : ℚ) :
    profileIntegralBoxSparse g lam = (profileWeights g lam).integralBox g.cache.integrals g.left g.right := by
  simp only [profileIntegralBoxSparse]
  split
  · rename_i condition
    obtain ⟨first, second, selector⟩ := condition
    let weights := capacities g.left g.right
    have zeroWeights : profileWeights g lam = ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩ := by
      simpa only [profileWeights] using
        conjugateWeights_eq_zero_of_gates g.cache.rangeA g.cache.rangeB lam
          weights.L weights.K weights.V first second selector
    rw [zeroWeights, ← LeafWeights.integralBoxSparse_eq]
    simp [LeafWeights.integralBoxSparse, FixedBox.mulRatSkippingZero, FixedBox.add]
  · exact LeafWeights.integralBoxSparse_eq _ _ _ _

def profileIntegralSparseCheck (mode : Fin 20) (tauNumerator : ℤ) (leaf : ProfileLeaf) : Bool :=
  let g := leaf.geometry.val
  capacityCheck g.left g.right &&
  slopeIntegerCheck mode tauNumerator leaf.cell g.left g.right leaf.lam &&
  decide (leaf.lower ≤ (profileIntegralBoxSparse g leaf.lam).lo)

theorem profileIntegralSparseCheck_eq (mode : Fin 20) (tauNumerator : ℤ) (leaf : ProfileLeaf) :
    profileIntegralSparseCheck mode tauNumerator leaf = profileIntegerCheck mode tauNumerator leaf := by
  simp only [profileIntegralSparseCheck, profileIntegerCheck, profileIntegralBoxSparse_eq]

theorem all_profile_check_of_integral_sparse {mode : Fin 20} {tauNumerator : ℤ}
    (tau : FrontierWitnesses.modeTau mode = (tauNumerator : ℚ) / 1000000000000000000)
    {leaves : List ProfileLeaf}
    (checked : leaves.all (fun leaf => profileIntegralSparseCheck mode tauNumerator leaf) = true) :
    leaves.all (fun leaf => leaf.check mode) = true := by
  apply all_profile_check_of_integer tau
  simpa only [profileIntegralSparseCheck_eq] using checked

end

public section

macro "erdos_profile_integral_sparse_decide " tau:term : tactic =>
  `(tactic| (
    apply all_profile_check_of_integral_sparse $tau
    erdos_leaves_decide
  ))


macro "erdos_profile_integer_decide " tau:term : tactic =>
  `(tactic| (
    apply all_profile_check_of_integral_sparse $tau
    erdos_leaves_decide
  ))

end
end ErdosOverlap.FrontierLeaves
