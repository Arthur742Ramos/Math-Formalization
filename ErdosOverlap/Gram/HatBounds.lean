/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Gram.HatBaseline

/-! # Nonnegative physical hats and preservation of an overlap cap -/

open MeasureTheory Set
open scoped Convolution

namespace ErdosOverlap.Gram

public section
noncomputable section

theorem wholeOverlap_nonneg {h : ℝ → ℝ} (hh : Admissible h) (t : ℝ) :
    0 ≤ wholeOverlap h t := by
  by_cases ht : t ∈ Icc (-2 : ℝ) 2
  · by_cases ht0 : 0 ≤ t
    · rw [wholeOverlap_eq_positive h ⟨ht0, ht.2⟩]
      exact positiveOverlap_nonneg hh ⟨ht0, ht.2⟩
    · have hn : -t ∈ Icc (0 : ℝ) 2 := ⟨by linarith, by linarith [ht.1]⟩
      have heq := wholeOverlap_neg_eq_negative h hn
      rw [neg_neg] at heq
      rw [heq]
      exact negativeOverlap_nonneg hh hn
  · rw [wholeOverlap_eq_zero_off_support h ht]

theorem wholeOverlap_le_cap {h : ℝ → ℝ} {M : ℝ}
    (hh : Admissible h) (hcap : OverlapCap h M) (t : ℝ) : wholeOverlap h t ≤ M := by
  by_cases ht : t ∈ Icc (-2 : ℝ) 2
  · by_cases ht0 : 0 ≤ t
    · rw [wholeOverlap_eq_positive h ⟨ht0, ht.2⟩]
      exact (hcap t ⟨ht0, ht.2⟩).1
    · have hn : -t ∈ Icc (0 : ℝ) 2 := ⟨by linarith, by linarith [ht.1]⟩
      have heq := wholeOverlap_neg_eq_negative h hn
      rw [neg_neg] at heq
      rw [heq]
      exact (hcap (-t) hn).2
  · rw [wholeOverlap_eq_zero_off_support h ht]
    exact hcap.nonneg hh

theorem evenOverlap_nonneg {h : ℝ → ℝ} (hh : Admissible h) (t : ℝ) :
    0 ≤ evenOverlap h t := by
  unfold evenOverlap
  exact div_nonneg (add_nonneg (wholeOverlap_nonneg hh t) (wholeOverlap_nonneg hh (-t)))
    (by norm_num)

theorem evenOverlap_le_cap {h : ℝ → ℝ} {M : ℝ}
    (hh : Admissible h) (hcap : OverlapCap h M) (t : ℝ) : evenOverlap h t ≤ M := by
  have hp := wholeOverlap_le_cap hh hcap t
  have hn := wholeOverlap_le_cap hh hcap (-t)
  unfold evenOverlap
  linarith

theorem tent_integrable {a : ℝ} (ha : 0 < a) : Integrable (tent a) := by
  have hi := (phaseWindow_integrable a).comp_neg.integrable_convolution
    (ContinuousLinearMap.mul ℝ ℝ) (phaseWindow_integrable a)
  apply (hi.div_const a).congr
  filter_upwards with t
  rw [← correlation_eq_reflected_convolution, phaseWindow_autocorrelation, ← tent_mul_scale ha]
  field_simp

theorem tent_translate_integrable {a : ℝ} (ha : 0 < a) (z : ℝ) :
    Integrable (fun t => tent a (t - z)) := by
  convert! (tent_integrable ha).comp_sub_right z using 1

theorem tent_whole_integral {a : ℝ} (ha : 0 < a) (z : ℝ) :
    (∫ t : ℝ, tent a (t - z)) = a := by
  have hi := tent_weighted_integral_translate (fun _ => (1 : ℝ)) ha z
  simp only [one_mul] at hi
  rw [hi, tent_interval_integral ha]

theorem hatOverlap_nonneg {h : ℝ → ℝ} (hh : Admissible h)
    {a : ℝ} (ha : 0 < a) (z : ℝ) : 0 ≤ hatOverlap h a z := by
  unfold hatOverlap
  apply div_nonneg _ ha.le
  apply integral_nonneg
  intro t
  exact mul_nonneg (evenOverlap_nonneg hh t) (tent_nonneg a (t - z))

theorem hatOverlap_le_cap {h : ℝ → ℝ} {M a : ℝ}
    (hh : Admissible h) (hcap : OverlapCap h M) (ha : 0 < a) (z : ℝ) :
    hatOverlap h a z ≤ M := by
  unfold hatOverlap
  apply (div_le_iff₀ ha).mpr
  calc
    _ ≤ ∫ t : ℝ, M * tent a (t - z) := by
      apply integral_mono (weighted_integrable_tent (evenOverlap_integrable hh) ha z)
        ((tent_translate_integrable ha z).const_mul M)
      intro t
      exact mul_le_mul_of_nonneg_right (evenOverlap_le_cap hh hcap t) (tent_nonneg a (t - z))
    _ = _ := by rw [integral_const_mul, tent_whole_integral ha z]

end
end
end ErdosOverlap.Gram
