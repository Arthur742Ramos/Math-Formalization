/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Pointwise
public import Mathlib.Algebra.Order.Group.MinMax

/-!
# Sharp error propagation for the physical scalar conjugate

The kernel coefficients enter the cost through absolute values and a positive
part. These estimates do not require a sign decision for either coefficient.
They therefore remain valid on cells containing zeros of the true kernel.
-/

namespace ErdosOverlap.Numerics

public section

theorem radial_B_cost_eq_max {B L x : ℝ} (hx : 0 ≤ x) :
    |B| * x + max B 0 * max (L - x) 0 =
      max (B * max L x) (-B * x) := by
  have hm : 0 ≤ max L x := hx.trans (le_max_right _ _)
  have hid : x + max (L - x) 0 = max L x := by
    by_cases h : x ≤ L
    · rw [max_eq_left (sub_nonneg.mpr h), max_eq_left h]
      ring
    · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h)),
        max_eq_right (le_of_not_ge h)]
      ring
  by_cases hB : 0 ≤ B
  · rw [abs_of_nonneg hB, max_eq_left hB]
    have hprod : -B * x ≤ B * max L x := by
      exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hB) hx).trans
        (mul_nonneg hB hm)
    rw [max_eq_left hprod, ← mul_add, hid]
  · have hB' : B ≤ 0 := le_of_not_ge hB
    rw [abs_of_nonpos hB', max_eq_right hB']
    have hprod : B * max L x ≤ -B * x := by
      exact (mul_nonpos_of_nonpos_of_nonneg hB' hm).trans
        (mul_nonneg (neg_nonneg.mpr hB') hx)
    rw [max_eq_right hprod]
    ring

theorem radial_B_cost_abs_sub_le {B B' L U x : ℝ}
    (hx : 0 ≤ x) (hxU : x ≤ U) :
    |(|B| * x + max B 0 * max (L - x) 0) -
      (|B'| * x + max B' 0 * max (L - x) 0)| ≤
      max L U * |B - B'| := by
  rw [radial_B_cost_eq_max hx, radial_B_cost_eq_max hx]
  apply (abs_max_sub_max_le_max _ _ _ _).trans
  apply max_le
  · calc
      |B * max L x - B' * max L x| = max L x * |B - B'| := by
        rw [← sub_mul, abs_mul, abs_of_nonneg (hx.trans (le_max_right _ _))]
        ring
      _ ≤ max L U * |B - B'| :=
        mul_le_mul_of_nonneg_right (max_le_max_left L hxU) (abs_nonneg _)
  · calc
      |-B * x - -B' * x| = x * |B - B'| := by
        have he : -B * x - -B' * x = -(B - B') * x := by ring
        rw [he, abs_mul, abs_neg, abs_of_nonneg hx]
        ring
      _ ≤ max L U * |B - B'| :=
        mul_le_mul_of_nonneg_right (hxU.trans (le_max_right _ _)) (abs_nonneg _)

/-- The kernel-cost error has coefficient `U` for the first kernel value and
`max L U` for its reflected value. -/
theorem physical_profileCost_abs_sub_le {A A' B B' L U z : ℝ}
    (hz : |z| ≤ U) :
    |profileCost (max B 0) (|A| + |B|) L z -
      profileCost (max B' 0) (|A'| + |B'|) L z| ≤
      U * |A - A'| + max L U * |B - B'| := by
  have hB := radial_B_cost_abs_sub_le (B := B) (B' := B') (L := L)
    (abs_nonneg z) hz
  have hA : abs ((abs A - abs A') * abs z) ≤ U * |A - A'| := by
    rw [abs_mul, abs_abs]
    calc
      abs (abs A - abs A') * |z| ≤ |A - A'| * |z| :=
        mul_le_mul_of_nonneg_right (abs_abs_sub_abs_le_abs_sub A A') (abs_nonneg z)
      _ ≤ |A - A'| * U := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      _ = U * |A - A'| := mul_comm _ _
  have he : profileCost (max B 0) (|A| + |B|) L z -
      profileCost (max B' 0) (|A'| + |B'|) L z =
      (|A| - |A'|) * |z| +
        ((|B| * |z| + max B 0 * max (L - |z|) 0) -
         (|B'| * |z| + max B' 0 * max (L - |z|) 0)) := by
    unfold profileCost
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hA hB)

/-- One-sided perturbation bound, obtained by testing the old conjugate at
an actual attaining point of the perturbed cost. -/
theorem physical_profileConjugate_sub_le {A A' B B' L U lam lam' : ℝ}
    (hL : 0 ≤ L) (hU : 0 ≤ U) :
    profileConjugate (max B 0) (|A| + |B|) L U lam -
      profileConjugate (max B' 0) (|A'| + |B'|) L U lam' ≤
      U * |A - A'| + max L U * |B - B'| + U * |lam - lam'| := by
  have hb : 0 ≤ max B' 0 := le_max_right _ _
  have hbc : max B' 0 ≤ |A'| + |B'| := by
    apply max_le
    · exact (le_abs_self B').trans (by linarith [abs_nonneg A'])
    · positivity
  obtain ⟨z, hz, _, heq⟩ := profileConjugate_exists_attainer hb hbc hL hU
    (lam := lam')
  have hlow := profileConjugate_le_cost_sub_linear_of_abs_le
    (b := max B 0) (c := |A| + |B|) (lam := lam) hL hU hz
  have hcost := (le_abs_self _).trans (physical_profileCost_abs_sub_le
    (A := A) (A' := A') (B := B) (B' := B') (L := L) hz)
  have hlin : (lam' - lam) * z ≤ U * |lam - lam'| := by
    calc
      (lam' - lam) * z ≤ |(lam' - lam) * z| := le_abs_self _
      _ = |lam - lam'| * |z| := by rw [abs_mul, abs_sub_comm]
      _ ≤ |lam - lam'| * U := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      _ = U * |lam - lam'| := mul_comm _ _
  linarith

/-- Sharp simultaneous perturbation control of both kernel values and the
linear dual coefficient, valid across all sign and hinge transitions. -/
theorem physical_profileConjugate_abs_sub_le {A A' B B' L U lam lam' : ℝ}
    (hL : 0 ≤ L) (hU : 0 ≤ U) :
    |profileConjugate (max B 0) (|A| + |B|) L U lam -
      profileConjugate (max B' 0) (|A'| + |B'|) L U lam'| ≤
      U * |A - A'| + max L U * |B - B'| + U * |lam - lam'| := by
  apply abs_le.mpr
  constructor
  · have h := physical_profileConjugate_sub_le (A := A') (A' := A)
      (B := B') (B' := B) (lam := lam') (lam' := lam) hL hU
    rw [abs_sub_comm A' A, abs_sub_comm B' B, abs_sub_comm lam' lam] at h
    linarith
  · exact physical_profileConjugate_sub_le hL hU

/-- Uniform kernel approximations with exact linear dual coefficient. -/
theorem physical_profileConjugate_error_le
    {A A' B B' L U lam δA δB : ℝ}
    (hL : 0 ≤ L) (hU : 0 ≤ U)
    (hA : |A - A'| ≤ δA) (hB : |B - B'| ≤ δB) :
    |profileConjugate (max B 0) (|A| + |B|) L U lam -
      profileConjugate (max B' 0) (|A'| + |B'|) L U lam| ≤
      U * δA + max L U * δB := by
  have h := physical_profileConjugate_abs_sub_le (A := A) (A' := A')
    (B := B) (B' := B') (lam := lam) (lam' := lam) hL hU
  simp only [sub_self, abs_zero, mul_zero, add_zero] at h
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hA hU)
    (mul_le_mul_of_nonneg_left hB (hU.trans (le_max_right _ _))))

end
end ErdosOverlap.Numerics
