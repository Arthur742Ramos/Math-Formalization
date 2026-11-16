/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.IntervalCell

/-!
# Exact interpolation between consecutive integer lags

On each grid interval only the two neighboring integer tents can be
nonzero. Both endpoints are included; the formula therefore applies
without a separate convention for integral grid shifts.
-/

namespace ErdosOverlap.Discrete

public section

theorem integer_grid_tent (δ : ℝ) (hδ : 0 < δ) (k d : ℤ) (t : ℝ)
    (hl : (k : ℝ) * δ ≤ t) (hu : t ≤ ((k + 1 : ℤ) : ℝ) * δ) :
    max (δ - |t - (d : ℝ) * δ|) 0 =
      (if d = k then ((k + 1 : ℤ) : ℝ) * δ - t else 0) +
      (if d = k + 1 then t - (k : ℝ) * δ else 0) := by
  have hu' : t ≤ ((k : ℝ) + 1) * δ := by
    simpa only [Int.cast_add, Int.cast_one] using hu
  by_cases hd : d = k
  · subst d
    have hn : 0 ≤ δ - (t - (k : ℝ) * δ) := by nlinarith [hu']
    rw [abs_of_nonneg (sub_nonneg.mpr hl), max_eq_left hn, if_pos rfl,
      if_neg (by omega : k ≠ k + 1), add_zero]
    push_cast
    ring
  by_cases hd1 : d = k + 1
  · subst d
    have hn : 0 ≤ δ - (-(t - ((k + 1 : ℤ) : ℝ) * δ)) := by
      push_cast
      nlinarith [hl]
    rw [abs_of_nonpos (sub_nonpos.mpr hu), max_eq_left hn,
      if_neg (by omega : (k + 1 : ℤ) ≠ k), if_pos rfl, zero_add]
    push_cast
    ring
  rw [if_neg hd, if_neg hd1, zero_add]
  apply max_eq_right
  have hfar : d + 1 ≤ k ∨ k + 2 ≤ d := by omega
  rcases hfar with hfar | hfar
  · have hr : (d : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hfar
    have hm := mul_le_mul_of_nonneg_right hr hδ.le
    have ha := le_abs_self (t - (d : ℝ) * δ)
    nlinarith [hl, hm, ha]
  · have hr : (k : ℝ) + 2 ≤ (d : ℝ) := by exact_mod_cast hfar
    have hm := mul_le_mul_of_nonneg_right hr hδ.le
    have ha := neg_le_abs (t - (d : ℝ) * δ)
    nlinarith [hu', hm, ha]

end
end ErdosOverlap.Discrete
