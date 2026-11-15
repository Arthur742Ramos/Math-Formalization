/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Gram.TentLag

/-!
# Physical contrast autocorrelation and overlap hat averages

The contrast identity relates the phase covariance to the original two-color
overlap, including the exact factor of four and the endpoint conventions.
-/

open MeasureTheory Set
open scoped Convolution

namespace ErdosOverlap.Gram

public section
noncomputable section

@[expose] def evenOverlap (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  (wholeOverlap h t + wholeOverlap h (-t)) / 2

@[expose] def hatOverlap (h : ℝ → ℝ) (a z : ℝ) : ℝ :=
  (∫ t : ℝ, evenOverlap h t * tent a (t - z)) / a

@[expose] def hatBaseline (a z : ℝ) : ℝ :=
  (∫ t : ℝ, max (2 - |t|) 0 * tent a (t - z)) / (4 * a)

theorem supportedDensity_abs_le_one {h : ℝ → ℝ} (hh : Admissible h) (x : ℝ) :
    |supportedDensity h x| ≤ 1 := by
  by_cases hx : x ∈ Icc (0 : ℝ) 2
  · simp only [supportedDensity, indicator_of_mem hx, abs_of_nonneg (hh.nonneg x hx)]
    exact hh.le_one x hx
  · simp [supportedDensity, hx]

theorem supportedComplement_abs_le_one {h : ℝ → ℝ} (hh : Admissible h) (x : ℝ) :
    |supportedComplement h x| ≤ 1 := by
  by_cases hx : x ∈ Icc (0 : ℝ) 2
  · have hn : 0 ≤ 1 - h x := by linarith [hh.le_one x hx]
    simp only [supportedComplement, indicator_of_mem hx, abs_of_nonneg hn]
    linarith [hh.nonneg x hx]
  · simp [supportedComplement, hx]

theorem correlation_integrable_of_bounded {f g : ℝ → ℝ} {C : ℝ}
    (hf : Integrable f) (hg : Measurable g) (hgb : ∀ x, |g x| ≤ C) (t : ℝ) :
    Integrable (fun x => f x * g (x + t)) := by
  have hi : Integrable (fun x => g (x + t) * f x) := by
    apply hf.bdd_mul (hg.comp (measurable_id.add_const t)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using hgb (x + t))
  exact hi.congr (Filter.Eventually.of_forall (fun x => mul_comm _ _))

theorem contrast_product_identity (h : ℝ → ℝ) (x t : ℝ) :
    contrast h x * contrast h (x + t) =
      phaseWindow 2 x * phaseWindow 2 (x + t) -
        2 * (supportedDensity h x * supportedComplement h (x + t) +
          supportedComplement h x * supportedDensity h (x + t)) := by
  by_cases hx : x ∈ Icc (0 : ℝ) 2 <;>
    by_cases hxt : x + t ∈ Icc (0 : ℝ) 2 <;>
    simp [contrast, phaseWindow, supportedDensity, supportedComplement, hx, hxt]
  all_goals ring

theorem reverse_correlation_eq_wholeOverlap (h : ℝ → ℝ) (t : ℝ) :
    (∫ x : ℝ, supportedComplement h x * supportedDensity h (x + t)) =
      wholeOverlap h (-t) := by
  have hs := integral_add_right_eq_self
    (fun x : ℝ => supportedDensity h x * supportedComplement h (x - t)) t (μ := volume)
  calc
    _ = ∫ x : ℝ, supportedDensity h (x + t) * supportedComplement h ((x + t) - t) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [add_sub_cancel_right]
      exact mul_comm _ _
    _ = ∫ x : ℝ, supportedDensity h x * supportedComplement h (x - t) := hs
    _ = _ := by simp only [wholeOverlap, sub_eq_add_neg]

/-- Exact contrast-to-overlap identity on the full real line. -/
theorem contrastAutocorrelation_eq {h : ℝ → ℝ} (hh : Admissible h) (t : ℝ) :
    contrastAutocorrelation h t = max (2 - |t|) 0 -
      2 * (wholeOverlap h t + wholeOverlap h (-t)) := by
  have hb := correlation_integrable_of_bounded (phaseWindow_integrable 2)
    (phaseWindow_measurable 2) (phaseWindow_abs_le_one 2) t
  have hp := correlation_integrable_of_bounded (supportedDensity_integrable hh)
    (supportedComplement_measurable hh) (supportedComplement_abs_le_one hh) t
  have hn := correlation_integrable_of_bounded (supportedComplement_integrable hh)
    (supportedDensity_measurable hh) (supportedDensity_abs_le_one hh) t
  have hpn : Integrable (fun x =>
      supportedDensity h x * supportedComplement h (x + t) +
        supportedComplement h x * supportedDensity h (x + t)) := by
    convert! hp.add hn using 1
  unfold contrastAutocorrelation
  calc
    _ = ∫ x : ℝ, phaseWindow 2 x * phaseWindow 2 (x + t) -
        2 * (supportedDensity h x * supportedComplement h (x + t) +
          supportedComplement h x * supportedDensity h (x + t)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => contrast_product_identity h x t)
    _ = _ := by
      rw [integral_sub hb (hpn.const_mul 2), integral_const_mul,
        integral_add hp hn, phaseWindow_autocorrelation,
        reverse_correlation_eq_wholeOverlap]
      rfl

theorem evenOverlap_eq_contrast {h : ℝ → ℝ} (hh : Admissible h) (t : ℝ) :
    evenOverlap h t = (max (2 - |t|) 0 - contrastAutocorrelation h t) / 4 := by
  rw [contrastAutocorrelation_eq hh t]
  unfold evenOverlap
  ring

theorem evenOverlap_eq_signed (h : ℝ → ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 2) :
    evenOverlap h t = (positiveOverlap h t + negativeOverlap h t) / 2 := by
  rw [evenOverlap, wholeOverlap_eq_positive h ht, wholeOverlap_neg_eq_negative h ht]

theorem evenOverlap_integrable {h : ℝ → ℝ} (hh : Admissible h) :
    Integrable (evenOverlap h) := by
  exact ((wholeOverlap_integrable hh).add (wholeOverlap_integrable hh).comp_neg).div_const 2

theorem tent_continuous (a : ℝ) : Continuous (tent a) := by
  unfold tent
  exact (continuous_const.sub (continuous_abs.div_const a)).max continuous_const

theorem tent_nonneg (a t : ℝ) : 0 ≤ tent a t := le_max_right _ _

theorem tent_abs_le_one {a : ℝ} (ha : 0 < a) (t : ℝ) : |tent a t| ≤ 1 := by
  rw [abs_of_nonneg (tent_nonneg a t)]
  unfold tent
  apply max_le _ zero_le_one
  have hp := div_nonneg (abs_nonneg t) ha.le
  linarith

theorem weighted_integrable_tent {f : ℝ → ℝ} (hf : Integrable f)
    {a : ℝ} (ha : 0 < a) (z : ℝ) :
    Integrable (fun t => f t * tent a (t - z)) := by
  have hi : Integrable (fun t => tent a (t - z) * f t) := by
    apply hf.bdd_mul ((tent_continuous a).comp (continuous_id.sub continuous_const)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, Pi.sub_apply, id_eq] using tent_abs_le_one ha (t - z))
  exact hi.congr (Filter.Eventually.of_forall (fun t => mul_comm _ _))

theorem overlapTriangle_integrable : Integrable (fun t : ℝ => max (2 - |t|) 0) := by
  have hi := (phaseWindow_integrable 2).comp_neg.integrable_convolution
    (ContinuousLinearMap.mul ℝ ℝ) (phaseWindow_integrable 2)
  apply hi.congr
  filter_upwards with t
  rw [← correlation_eq_reflected_convolution, phaseWindow_autocorrelation]

/-- Every physical hat average is exactly the baseline minus the covariance lag. -/
theorem hatOverlap_eq_covariance {h : ℝ → ℝ} (hh : Admissible h)
    {a : ℝ} (ha : 0 < a) {N k : ℕ} (hk : k ≤ N) (hNa : (N : ℝ) * a = 2) :
    hatOverlap h a ((k : ℝ) * a) = hatBaseline a ((k : ℝ) * a) -
      (a / 4) * ∑ i ∈ Finset.range (N - k + 1), covariance h a i (i + k) := by
  have hb := weighted_integrable_tent overlapTriangle_integrable ha ((k : ℝ) * a)
  have hr := weighted_integrable_tent (contrastAutocorrelation_integrable hh) ha ((k : ℝ) * a)
  have heq : (∫ t : ℝ, evenOverlap h t * tent a (t - (k : ℝ) * a)) =
      ((∫ t : ℝ, max (2 - |t|) 0 * tent a (t - (k : ℝ) * a)) -
        (∫ t : ℝ, contrastAutocorrelation h t * tent a (t - (k : ℝ) * a))) / 4 := by
    calc
      _ = ∫ t : ℝ, (max (2 - |t|) 0 * tent a (t - (k : ℝ) * a) -
          contrastAutocorrelation h t * tent a (t - (k : ℝ) * a)) * (1 / 4) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [evenOverlap_eq_contrast hh t]
        ring
      _ = _ := by rw [integral_mul_const, integral_sub hb hr]; ring
  unfold hatOverlap hatBaseline
  rw [heq, ← covariance_tent_identity hh ha hk hNa]
  field_simp

end
end
end ErdosOverlap.Gram
