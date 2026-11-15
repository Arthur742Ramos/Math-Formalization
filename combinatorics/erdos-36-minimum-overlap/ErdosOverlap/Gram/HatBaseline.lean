/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Gram.ContrastOverlap

/-! # Exact triangular-support baseline integrals for all phase lags -/

open MeasureTheory Set

namespace ErdosOverlap.Gram

public section
noncomputable section

theorem tent_eq_zero_of_le_abs {a t : ℝ} (ha : 0 < a) (ht : a ≤ |t|) :
    tent a t = 0 := by
  unfold tent
  apply max_eq_right
  have h : (1 : ℝ) ≤ |t| / a := (le_div_iff₀ ha).mpr (by simpa using ht)
  linarith

theorem tent_eq_of_abs_le {a t : ℝ} (ha : 0 < a) (ht : |t| ≤ a) :
    tent a t = 1 - |t| / a := by
  unfold tent
  apply max_eq_left
  have h := (div_le_one ha).mpr ht
  linarith

theorem tent_eq_on_right {a t : ℝ} (ha : 0 < a) (ht : t ∈ Icc (0 : ℝ) a) :
    tent a t = 1 - t / a := by
  have habs : |t| ≤ a := by rw [abs_of_nonneg ht.1]; exact ht.2
  rw [tent_eq_of_abs_le ha habs, abs_of_nonneg ht.1]

theorem integral_left_reflect (F : ℝ → ℝ) (a : ℝ) :
    (∫ t in -a..(0 : ℝ), F t) = ∫ t in (0 : ℝ)..a, F (-t) := by
  simpa only [zero_sub, sub_zero] using
    (intervalIntegral.integral_comp_sub_left F (a := 0) (b := a) 0).symm

theorem integral_symmetric_even {F : ℝ → ℝ} (hF : Continuous F)
    (heven : ∀ t, F (-t) = F t) (a : ℝ) :
    (∫ t in -a..a, F t) = 2 * ∫ t in (0 : ℝ)..a, F t := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable (a := -a) (b := 0)) (hF.intervalIntegrable (a := 0) (b := a)),
    integral_left_reflect]
  simp_rw [heven]
  ring

theorem integral_symmetric_odd {F : ℝ → ℝ} (hF : Continuous F)
    (hodd : ∀ t, F (-t) = -F t) (a : ℝ) :
    (∫ t in -a..a, F t) = 0 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hF.intervalIntegrable (a := -a) (b := 0)) (hF.intervalIntegrable (a := 0) (b := a)),
    integral_left_reflect]
  simp_rw [hodd, intervalIntegral.integral_neg]
  ring

theorem tent_half_integral {a : ℝ} (ha : 0 < a) :
    (∫ t in (0 : ℝ)..a, tent a t) = a / 2 := by
  calc
    _ = ∫ t in (0 : ℝ)..a, 1 - t / a := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le ha.le] at ht
      exact tent_eq_on_right ha ht
    _ = _ := by
      have hi : IntervalIntegrable (fun t : ℝ => t / a) volume 0 a := by
        convert! (continuous_id.div_const a).intervalIntegrable (μ := volume) 0 a using 1
      rw [intervalIntegral.integral_sub intervalIntegrable_const hi,
        intervalIntegral.integral_div, integral_id]
      simp only [intervalIntegral.integral_const, sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
        smul_eq_mul, mul_one]
      field_simp
      norm_num

theorem tent_half_firstMoment {a : ℝ} (ha : 0 < a) :
    (∫ t in (0 : ℝ)..a, t * tent a t) = a ^ 2 / 6 := by
  calc
    _ = ∫ t in (0 : ℝ)..a, t - t ^ 2 / a := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le ha.le] at ht
      change t * tent a t = _
      rw [tent_eq_on_right ha ht]
      ring
    _ = _ := by
      have hi : IntervalIntegrable (fun t : ℝ => t ^ 2 / a) volume 0 a := by
        convert! ((continuous_id.pow 2).div_const a).intervalIntegrable (μ := volume) 0 a using 1
      have hid : IntervalIntegrable (fun t : ℝ => t) volume 0 a := by
        convert! continuous_id.intervalIntegrable (μ := volume) 0 a using 1
      rw [intervalIntegral.integral_sub hid hi,
        intervalIntegral.integral_div, integral_id, integral_pow]
      norm_num
      field_simp
      norm_num

theorem tent_interval_integral {a : ℝ} (ha : 0 < a) :
    (∫ t in -a..a, tent a t) = a := by
  rw [integral_symmetric_even (tent_continuous a) (tent_even a), tent_half_integral ha]
  ring

theorem tent_absMoment_integral {a : ℝ} (ha : 0 < a) :
    (∫ t in -a..a, |t| * tent a t) = a ^ 2 / 3 := by
  have hpos : (∫ t in (0 : ℝ)..a, |t| * tent a t) = a ^ 2 / 6 := by
    calc
      _ = ∫ t in (0 : ℝ)..a, t * tent a t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le ha.le] at ht
        dsimp only
        rw [abs_of_nonneg ht.1]
      _ = _ := tent_half_firstMoment ha
  have hf : Continuous (fun t : ℝ => |t| * tent a t) := by
    convert! continuous_abs.mul (tent_continuous a) using 1
  rw [integral_symmetric_even hf (fun t => by simp only [abs_neg, tent_even]) a, hpos]
  ring

theorem tent_firstMoment_integral {a : ℝ} :
    (∫ t in -a..a, t * tent a t) = 0 := by
  have hf : Continuous (fun t : ℝ => t * tent a t) := by
    convert! continuous_id.mul (tent_continuous a) using 1
  apply integral_symmetric_odd hf
  intro t
  rw [tent_even, neg_mul]

theorem tent_weighted_integral_restrict (F : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (z : ℝ) :
    (∫ t : ℝ, F t * tent a (t - z)) =
      ∫ t in (z - a)..(z + a), F t * tent a (t - z) := by
  have hout : ∀ t, t ∉ Icc (z - a) (z + a) → F t * tent a (t - z) = 0 := by
    intro t ht
    have hn : ¬ |t - z| ≤ a := by
      intro hb
      rcases abs_le.mp hb with ⟨hl, hu⟩
      exact ht ⟨by linarith, by linarith⟩
    rw [tent_eq_zero_of_le_abs ha (le_of_lt (not_le.mp hn)), mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : z - a ≤ z + a)]

theorem tent_weighted_integral_translate (F : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (z : ℝ) :
    (∫ t : ℝ, F t * tent a (t - z)) =
      ∫ t in -a..a, F (t + z) * tent a t := by
  rw [tent_weighted_integral_restrict F ha z]
  have hs := intervalIntegral.integral_comp_add_right
    (fun t => F t * tent a (t - z)) (a := -a) (b := a) z
  have hl : -a + z = z - a := by ring
  have hr : a + z = z + a := add_comm _ _
  rw [hl, hr] at hs
  rw [← hs]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [add_sub_cancel_right]

theorem hatBaseline_zero {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2) :
    hatBaseline a 0 = 1 / 2 - a / 12 := by
  have heq : (∫ t : ℝ, max (2 - |t|) 0 * tent a (t - 0)) =
      2 * a - a ^ 2 / 3 := by
    rw [tent_weighted_integral_translate _ ha 0]
    simp only [add_zero]
    calc
      _ = ∫ t in -a..a, 2 * tent a t - |t| * tent a t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by linarith : -a ≤ a)] at ht
        have habs : |t| ≤ a := abs_le.mpr ht
        have hp : 0 ≤ 2 - |t| := by linarith
        dsimp only
        rw [max_eq_left hp]
        ring
      _ = _ := by
        have hi := (tent_continuous a).intervalIntegrable (μ := volume) (-a) a
        have hib : IntervalIntegrable (fun t : ℝ => |t| * tent a t) volume (-a) a := by
          convert! (continuous_abs.mul (tent_continuous a)).intervalIntegrable
            (μ := volume) (-a) a using 1
        rw [intervalIntegral.integral_sub (hi.const_mul 2) hib,
          intervalIntegral.integral_const_mul, tent_interval_integral ha, tent_absMoment_integral ha]
  unfold hatBaseline
  rw [heq]
  field_simp
  ring

theorem hatBaseline_interior {a z : ℝ} (ha : 0 < a) (hl : a ≤ z) (hu : z + a ≤ 2) :
    hatBaseline a z = (2 - z) / 4 := by
  have heq : (∫ t : ℝ, max (2 - |t|) 0 * tent a (t - z)) = (2 - z) * a := by
    rw [tent_weighted_integral_translate _ ha z]
    calc
      _ = ∫ t in -a..a, (2 - z) * tent a t - t * tent a t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by linarith : -a ≤ a)] at ht
        have hz0 : 0 ≤ t + z := by linarith [ht.1]
        have hz2 : t + z ≤ 2 := by linarith [ht.2]
        dsimp only
        rw [abs_of_nonneg hz0, max_eq_left (by linarith : 0 ≤ 2 - (t + z))]
        ring
      _ = _ := by
        have hi := (tent_continuous a).intervalIntegrable (μ := volume) (-a) a
        have hib : IntervalIntegrable (fun t : ℝ => t * tent a t) volume (-a) a := by
          convert! (continuous_id.mul (tent_continuous a)).intervalIntegrable
            (μ := volume) (-a) a using 1
        rw [intervalIntegral.integral_sub (hi.const_mul (2 - z)) hib,
          intervalIntegral.integral_const_mul, tent_interval_integral ha, tent_firstMoment_integral,
          sub_zero]
  unfold hatBaseline
  rw [heq]
  field_simp

theorem hatBaseline_last {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2) :
    hatBaseline a 2 = a / 24 := by
  let F : ℝ → ℝ := fun t => max (2 - |t + 2|) 0 * tent a t
  have hF : Continuous F :=
    ((continuous_const.sub ((continuous_id.add_const 2).abs)).max continuous_const).mul
      (tent_continuous a)
  have hleft : (∫ t in -a..(0 : ℝ), F t) = a ^ 2 / 6 := by
    rw [integral_left_reflect]
    calc
      _ = ∫ t in (0 : ℝ)..a, t * tent a t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le ha.le] at ht
        have hz : 0 ≤ -t + 2 := by linarith [ht.2]
        dsimp only [F]
        rw [abs_of_nonneg hz, tent_even]
        have he : 2 - (-t + 2) = t := by ring
        rw [he, max_eq_left ht.1]
      _ = _ := tent_half_firstMoment ha
  have hright : (∫ t in (0 : ℝ)..a, F t) = 0 := by
    calc
      _ = ∫ _t in (0 : ℝ)..a, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le ha.le] at ht
        dsimp only [F]
        rw [abs_of_nonneg (by linarith [ht.1] : 0 ≤ t + 2),
          max_eq_right (by linarith [ht.1] : 2 - (t + 2) ≤ 0), zero_mul]
      _ = _ := by simp
  have heq : (∫ t : ℝ, max (2 - |t|) 0 * tent a (t - 2)) = a ^ 2 / 6 := by
    rw [tent_weighted_integral_translate _ ha 2]
    change (∫ t in -a..a, F t) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (a := -a) (b := 0)) (hF.intervalIntegrable (a := 0) (b := a)),
      hleft, hright, add_zero]
  unfold hatBaseline
  rw [heq]
  field_simp
  norm_num

/-- A single exact formula for every grid baseline, with both endpoint cases. -/
theorem hatBaseline_grid {N k : ℕ} {a : ℝ} (ha : 0 < a)
    (hNa : (N : ℝ) * a = 2) (hk : k ≤ N) :
    hatBaseline a ((k : ℝ) * a) =
      if k = 0 then 1 / 2 - a / 12
      else if k = N then a / 24 else (2 - (k : ℝ) * a) / 4 := by
  have hN : 1 ≤ N := by
    by_contra hn
    have hz : N = 0 := by omega
    simp [hz] at hNa
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ha2 : a ≤ 2 := by nlinarith
  by_cases hk0 : k = 0
  · simp only [hk0, ite_true, Nat.cast_zero, zero_mul]
    exact hatBaseline_zero ha ha2
  · rw [ite_eq_right_iff.mpr (fun h => (hk0 h).elim)]
    by_cases hkN : k = N
    · simp only [hkN, ite_true, hNa]
      exact hatBaseline_last ha ha2
    · rw [ite_eq_right_iff.mpr (fun h => (hkN h).elim)]
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      have hkn : (k : ℝ) + 1 ≤ N := by exact_mod_cast (show k + 1 ≤ N by omega)
      exact hatBaseline_interior ha (by nlinarith) (by nlinarith)

theorem hatOverlap_eq_covariance_explicit {h : ℝ → ℝ} (hh : Admissible h)
    {N k : ℕ} {a : ℝ} (ha : 0 < a) (hNa : (N : ℝ) * a = 2) (hk : k ≤ N) :
    hatOverlap h a ((k : ℝ) * a) =
      (if k = 0 then 1 / 2 - a / 12
        else if k = N then a / 24 else (2 - (k : ℝ) * a) / 4) -
      (a / 4) * ∑ i ∈ Finset.range (N - k + 1), covariance h a i (i + k) := by
  rw [hatOverlap_eq_covariance hh ha hk hNa, hatBaseline_grid ha hNa hk]

end
end
end ErdosOverlap.Gram
