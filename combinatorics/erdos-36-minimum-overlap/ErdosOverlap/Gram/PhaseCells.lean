/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Pairing

/-!
# Physical phase cells of an arbitrary admissible measurable partition

The contrast is extended by zero outside `[0,2]`. Its primitive is globally
1-Lipschitz and vanishes outside that interval. Phase cell averages are exact
increments of this primitive; no discretization assumption is made on `h`.
-/

@[expose] public section

namespace ErdosOverlap.Gram

open MeasureTheory Set
open scoped Interval

noncomputable def contrast (h : ℝ → ℝ) : ℝ → ℝ :=
  (Icc (0 : ℝ) 2).indicator (fun x => 2 * h x - 1)

noncomputable def primitive (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, contrast h u

noncomputable def cellAverage (h : ℝ → ℝ) (a s : ℝ) (i : ℕ) : ℝ :=
  (primitive h (s + (i + 1 : ℕ) * a) - primitive h (s + (i : ℝ) * a)) / a

theorem contrast_measurable {h : ℝ → ℝ} (hh : Admissible h) :
    Measurable (contrast h) :=
  ((measurable_const.mul hh.measurable).sub_const 1).indicator measurableSet_Icc

theorem contrast_eq_zero_off_support (h : ℝ → ℝ) {x : ℝ}
    (hx : x ∉ Icc (0 : ℝ) 2) : contrast h x = 0 := by
  simp [contrast, hx]

theorem contrast_abs_le_one {h : ℝ → ℝ} (hh : Admissible h) (x : ℝ) :
    |contrast h x| ≤ 1 := by
  by_cases hx : x ∈ Icc (0 : ℝ) 2
  · simp only [contrast, indicator_of_mem hx]
    apply abs_le.mpr
    constructor <;> linarith [hh.nonneg x hx, hh.le_one x hx]
  · simp [contrast_eq_zero_off_support h hx]

theorem contrast_integrable {h : ℝ → ℝ} (hh : Admissible h) :
    Integrable (contrast h) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 2)).mp
  exact ((hh.intervalIntegrable (by norm_num) (by norm_num) (by norm_num)).const_mul 2).sub
    intervalIntegrable_const

theorem contrast_intervalIntegrable {h : ℝ → ℝ} (hh : Admissible h) (x y : ℝ) :
    IntervalIntegrable (contrast h) volume x y :=
  (contrast_integrable hh).intervalIntegrable

@[simp] theorem primitive_zero (h : ℝ → ℝ) : primitive h 0 = 0 := by
  simp [primitive]

theorem primitive_eq_on_support {h : ℝ → ℝ} (hh : Admissible h) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 2) :
    primitive h t = 2 * (∫ x in (0 : ℝ)..t, h x) - t := by
  have hi := hh.intervalIntegrable (by norm_num) ht.1 ht.2
  have heq : (∫ x in (0 : ℝ)..t, contrast h x) =
      ∫ x in (0 : ℝ)..t, 2 * h x - 1 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le ht.1] at hx
    have hx' : x ∈ Icc (0 : ℝ) 2 := ⟨hx.1, hx.2.trans ht.2⟩
    simp [contrast, hx']
  rw [primitive, heq, intervalIntegral.integral_sub (hi.const_mul 2)
    intervalIntegrable_const, intervalIntegral.integral_const_mul]
  simp

@[simp] theorem primitive_two {h : ℝ → ℝ} (hh : Admissible h) : primitive h 2 = 0 := by
  rw [primitive_eq_on_support hh (by norm_num), hh.mass]
  norm_num

theorem primitive_eq_zero_of_nonpos (h : ℝ → ℝ) {x : ℝ} (hx : x ≤ 0) :
    primitive h x = 0 := by
  have hi : (∫ u in x..(0 : ℝ), contrast h u) = 0 := by
    calc
      _ = ∫ _u in x..(0 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hx
        intro u hu
        exact contrast_eq_zero_off_support h (fun hmem => (not_le_of_gt hu.2) hmem.1)
      _ = 0 := by simp
  unfold primitive
  rw [intervalIntegral.integral_symm, hi, neg_zero]

theorem primitive_eq_zero_of_two_le {h : ℝ → ℝ} (hh : Admissible h)
    {x : ℝ} (hx : 2 ≤ x) : primitive h x = 0 := by
  have hi : (∫ u in (2 : ℝ)..x, contrast h u) = 0 := by
    calc
      _ = ∫ _u in (2 : ℝ)..x, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hx
        intro u hu
        exact contrast_eq_zero_off_support h (fun hmem => (not_le_of_gt hu.1) hmem.2)
      _ = 0 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (contrast_intervalIntegrable hh 0 2) (contrast_intervalIntegrable hh 2 x)
  change primitive h 2 + _ = primitive h x at hadd
  rw [primitive_two hh, hi, zero_add] at hadd
  exact hadd.symm

theorem primitive_lipschitz {h : ℝ → ℝ} (hh : Admissible h) :
    LipschitzWith 1 (primitive h) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hb : ∀ u ∈ Ι y x, ‖contrast h u‖ ≤ (1 : ℝ) := by
    intro u _
    simpa only [Real.norm_eq_abs] using contrast_abs_le_one hh u
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simp only [Real.norm_eq_abs, one_mul] at hn
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, primitive]
  rw [intervalIntegral.integral_interval_sub_left (contrast_intervalIntegrable hh 0 x)
    (contrast_intervalIntegrable hh 0 y)]
  exact hn

theorem primitive_continuous {h : ℝ → ℝ} (hh : Admissible h) :
    Continuous (primitive h) := (primitive_lipschitz hh).continuous

theorem cellAverage_eq_integral {h : ℝ → ℝ} (hh : Admissible h)
    (a s : ℝ) (i : ℕ) :
    cellAverage h a s i =
      (∫ u in (s + (i : ℝ) * a)..(s + (i + 1 : ℕ) * a), contrast h u) / a := by
  unfold cellAverage primitive
  rw [intervalIntegral.integral_interval_sub_left (contrast_intervalIntegrable hh _ _)
    (contrast_intervalIntegrable hh _ _)]

theorem cellAverage_continuous {h : ℝ → ℝ} (hh : Admissible h) (a : ℝ) (i : ℕ) :
    Continuous (fun s => cellAverage h a s i) := by
  unfold cellAverage
  exact ((primitive_continuous hh).comp (continuous_id.add continuous_const) |>.sub
    ((primitive_continuous hh).comp (continuous_id.add continuous_const))).div_const a

theorem cellAverage_abs_le_one {h : ℝ → ℝ} (hh : Admissible h)
    {a : ℝ} (ha : 0 < a) (s : ℝ) (i : ℕ) : |cellAverage h a s i| ≤ 1 := by
  have hl := (primitive_lipschitz hh).dist_le_mul
    (s + (i + 1 : ℕ) * a) (s + (i : ℝ) * a)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hl
  have hd : s + (i + 1 : ℕ) * a - (s + (i : ℝ) * a) = a := by
    push_cast
    ring
  rw [hd, abs_of_pos ha] at hl
  unfold cellAverage
  rw [abs_div, abs_of_pos ha]
  exact (div_le_one ha).mpr hl

end ErdosOverlap.Gram
