/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Gram.HatBounds
public import ErdosOverlap.PhaseKernel

/-! # The exact physical normalization of the shared phase-functional kernel -/

open MeasureTheory Set

namespace ErdosOverlap.Gram

public section
noncomputable section

@[expose] def symmetricHat (a z t : ℝ) : ℝ :=
  (tent a (t - z) + tent a (t + z)) / (2 * a)

theorem symmetricHat_continuous (a z : ℝ) : Continuous (symmetricHat a z) := by
  exact (((tent_continuous a).comp (continuous_id.sub continuous_const)).add
    ((tent_continuous a).comp (continuous_id.add continuous_const))).div_const (2 * a)

theorem symmetricHat_nonneg {a : ℝ} (ha : 0 < a) (z t : ℝ) :
    0 ≤ symmetricHat a z t := by
  unfold symmetricHat
  exact div_nonneg (add_nonneg (tent_nonneg _ _) (tent_nonneg _ _)) (by positivity)

theorem symmetricHat_abs_le {a : ℝ} (ha : 0 < a) (z t : ℝ) :
    |symmetricHat a z t| ≤ 1 / a := by
  rw [abs_of_nonneg (symmetricHat_nonneg ha z t)]
  unfold symmetricHat
  have h₁ := tent_abs_le_one ha (t - z)
  have h₂ := tent_abs_le_one ha (t + z)
  rw [abs_of_nonneg (tent_nonneg _ _)] at h₁ h₂
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * a)).mpr
  have heq : (1 / a) * (2 * a) = (2 : ℝ) := by field_simp
  rw [heq]
  linarith

theorem wholeOverlap_symmetricHat_integrable {h : ℝ → ℝ} (hh : Admissible h)
    {a : ℝ} (ha : 0 < a) (z : ℝ) :
    Integrable (fun t => symmetricHat a z t * wholeOverlap h t) := by
  apply (wholeOverlap_integrable hh).bdd_mul (symmetricHat_continuous a z).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    simpa only [Real.norm_eq_abs] using symmetricHat_abs_le ha z t)

/-- Symmetrizing a translated tent preserves its pairing with the even overlap. -/
theorem hatOverlap_eq_symmetricHat_pairing {h : ℝ → ℝ} (hh : Admissible h)
    {a : ℝ} (ha : 0 < a) (z : ℝ) :
    hatOverlap h a z = ∫ t : ℝ, symmetricHat a z t * wholeOverlap h t := by
  have hp := weighted_integrable_tent (wholeOverlap_integrable hh) ha z
  have hn := weighted_integrable_tent (wholeOverlap_integrable hh).comp_neg ha z
  have hplus : Integrable (fun t => wholeOverlap h t * tent a (t + z)) := by
    convert! weighted_integrable_tent (wholeOverlap_integrable hh) ha (-z) using 1
    simp only [sub_neg_eq_add]
  have hneg : (∫ t : ℝ, wholeOverlap h (-t) * tent a (t - z)) =
      ∫ t : ℝ, wholeOverlap h t * tent a (t + z) := by
    have hc := integral_neg_eq_self
      (fun t : ℝ => wholeOverlap h (-t) * tent a (t - z)) volume
    calc
      _ = ∫ t : ℝ, wholeOverlap h (-(-t)) * tent a (-t - z) := hc.symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with t
        rw [neg_neg, show -t - z = -(t + z) by ring, tent_even]
  have he : (∫ t : ℝ, evenOverlap h t * tent a (t - z)) =
      ((∫ t : ℝ, wholeOverlap h t * tent a (t - z)) +
        (∫ t : ℝ, wholeOverlap h t * tent a (t + z))) / 2 := by
    calc
      _ = ∫ t : ℝ, (wholeOverlap h t * tent a (t - z) +
          wholeOverlap h (-t) * tent a (t - z)) * (1 / 2) := by
        apply integral_congr_ae
        filter_upwards with t
        unfold evenOverlap
        ring
      _ = _ := by rw [integral_mul_const, integral_add hp hn, hneg]; ring
  have hs : (∫ t : ℝ, symmetricHat a z t * wholeOverlap h t) =
      ((∫ t : ℝ, wholeOverlap h t * tent a (t - z)) +
        (∫ t : ℝ, wholeOverlap h t * tent a (t + z))) / (2 * a) := by
    calc
      _ = ∫ t : ℝ, (wholeOverlap h t * tent a (t - z) +
          wholeOverlap h t * tent a (t + z)) * (1 / (2 * a)) := by
        apply integral_congr_ae
        filter_upwards with t
        unfold symmetricHat
        ring
      _ = _ := by rw [integral_mul_const, integral_add hp hplus]; ring
  unfold hatOverlap
  rw [he, hs]
  ring

theorem phaseHat_abs_eq_tent_pair {a z : ℝ} (ha : 0 < a) (hz : a ≤ z) (t : ℝ) :
    phaseHat a z |t| = tent a (t - z) + tent a (t + z) := by
  by_cases ht : 0 ≤ t
  · have hb : a ≤ |t + z| := by
      rw [abs_of_nonneg (by linarith : 0 ≤ t + z)]
      linarith
    rw [tent_eq_zero_of_le_abs ha hb, add_zero, abs_of_nonneg ht]
    rfl
  · have ht' : t ≤ 0 := le_of_not_ge ht
    have hb : a ≤ |t - z| := by
      rw [abs_of_nonpos (by linarith : t - z ≤ 0)]
      linarith
    rw [tent_eq_zero_of_le_abs ha hb, zero_add, abs_of_nonpos ht']
    unfold phaseHat tent
    rw [show -t - z = -(t + z) by ring, abs_neg]

theorem phaseKernel_eq_symmetricHat_sum {N : ℕ} (hN : 0 < N)
    (gamma : Array ℚ) (t : ℝ) :
    phaseKernel N gamma t = ∑ k ∈ Finset.range (N + 1),
      (gamma.getD k 0 : ℝ) * symmetricHat (2 / N) ((k : ℝ) * (2 / N)) t := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : (0 : ℝ) < 2 / N := by positivity
  rw [Finset.sum_range_succ']
  unfold phaseKernel
  simp only [Nat.cast_zero, zero_mul]
  rw [add_comm (∑ k ∈ Finset.range N,
    (gamma.getD (k + 1) 0 : ℝ) * symmetricHat (2 / N) ((k + 1 : ℕ) * (2 / N)) t)]
  congr 1
  · simp only [symmetricHat, phaseHat, tent, sub_zero, add_zero, abs_abs]
    ring
  · apply Finset.sum_congr rfl
    intro k _
    have hz : 2 / (N : ℝ) ≤ (k + 1 : ℕ) * (2 / N) := by
      have hk : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (Nat.succ_pos k)
      nlinarith
    rw [phaseHat_abs_eq_tent_pair ha hz]
    unfold symmetricHat
    ring

theorem phaseKernel_abs_le {N : ℕ} (hN : 0 < N) (gamma : Array ℚ) (t : ℝ) :
    |phaseKernel N gamma t| ≤
      ∑ k ∈ Finset.range (N + 1), |(gamma.getD k 0 : ℝ)| / (2 / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : (0 : ℝ) < 2 / N := by positivity
  rw [phaseKernel_eq_symmetricHat_sum hN gamma t]
  calc
    _ ≤ ∑ k ∈ Finset.range (N + 1),
        |(gamma.getD k 0 : ℝ) * symmetricHat (2 / N) ((k : ℝ) * (2 / N)) t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      have h := mul_le_mul_of_nonneg_left
        (symmetricHat_abs_le ha ((k : ℝ) * (2 / N)) t) (abs_nonneg (gamma.getD k 0 : ℝ))
      simpa only [mul_one_div] using h

/-- The literal kernel shared with the numerical compiler has exactly the
claimed physical functional, including the special zero-lag coefficient. -/
theorem phaseKernel_pairing_eq_hatOverlap_sum {h : ℝ → ℝ} (hh : Admissible h)
    {N : ℕ} (hN : 0 < N) (gamma : Array ℚ) :
    quartetFunctional h (phaseKernel N gamma) =
      ∑ k : Fin (N + 1), (gamma.getD k.val 0 : ℝ) *
        hatOverlap h (2 / N) ((k.val : ℝ) * (2 / N)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : (0 : ℝ) < 2 / N := by positivity
  have hwhole : (∫ t : ℝ, phaseKernel N gamma t * wholeOverlap h t) =
      quartetFunctional h (phaseKernel N gamma) := by
    rw [wholeOverlap_pairing_eq_squarePairing hh (phaseKernel_continuous N gamma).measurable
      (phaseKernel_abs_le hN gamma),
      squarePairing_eq_quartetFunctional_of_continuous hh
        (phaseKernel_continuous N gamma) (phaseKernel_even N gamma)]
  rw [← hwhole, Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (gamma.getD k 0 : ℝ) * hatOverlap h (2 / N) ((k : ℝ) * (2 / N)))]
  calc
    _ = ∫ t : ℝ, ∑ k ∈ Finset.range (N + 1), (gamma.getD k 0 : ℝ) *
        (symmetricHat (2 / N) ((k : ℝ) * (2 / N)) t * wholeOverlap h t) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [phaseKernel_eq_symmetricHat_sum hN gamma t, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ k ∈ Finset.range (N + 1), (gamma.getD k 0 : ℝ) *
        (∫ t : ℝ, symmetricHat (2 / N) ((k : ℝ) * (2 / N)) t * wholeOverlap h t) := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro k _
        exact integral_const_mul _ _
      · intro k _
        exact (wholeOverlap_symmetricHat_integrable hh ha ((k : ℝ) * (2 / N))).const_mul _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hatOverlap_eq_symmetricHat_pairing hh ha]

end
end
end ErdosOverlap.Gram
