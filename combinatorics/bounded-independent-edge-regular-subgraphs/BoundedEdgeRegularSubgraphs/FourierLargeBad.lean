module

public import BoundedEdgeRegularSubgraphs.FourierReplacement
import Mathlib.Tactic

/-!
# Fourier integral over phases with many bad available edges
-/

public section

open MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The integrand decays exponentially in the number of available edges
whose phase sum is farther than `η` from zero on the torus. -/
theorem degreeFourier_norm_le_torus_bad_count (A : Finset (Edge α))
    (q : Edge α → Set.Icc (0 : ℝ) 1) (d : α → ℤ) (t : α → PhaseCircle)
    {η lower : ℝ} (hη : 0 ≤ η) (hlower : 0 ≤ lower)
    (hq : ∀ e ∈ A, lower ≤ (q e : ℝ) * (1 - q e)) :
    ‖degreeFourier A q d t‖ ≤ Real.exp
      (-(2 * lower * Real.sin (η / 2) ^ 2) *
        ((A.filter fun e ↦ η < ‖t e.val.1 + t e.val.2‖).card : ℝ)) := by
  classical
  let c := 2 * lower * Real.sin (η / 2) ^ 2
  let P (e : Edge α) : Prop := η < ‖t e.val.1 + t e.val.2‖
  let weight (e : Edge α) := if P e then Real.exp (-c) else 1
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hpt (e : Edge α) (he : e ∈ A) :
      ‖phaseBernoulliFactor (q e) (t e.val.1 + t e.val.2)‖ ≤ weight e := by
    let s : PhaseCircle := t e.val.1 + t e.val.2
    refine (phaseBernoulliFactor_norm_le_exp (q e) s).trans ?_
    have hvar := hq e he
    have hw : 0 ≤ (q e : ℝ) * (1 - q e) := hlower.trans hvar
    by_cases h : P e
    · rw [show weight e = Real.exp (-c) by simp [weight, h]]
      apply Real.exp_le_exp.mpr
      have hs : ‖s‖ / 2 ≤ Real.pi / 2 := by linarith [phase_norm_le_pi s]
      have hsine : Real.sin (η / 2) ^ 2 ≤ Real.sin (‖s‖ / 2) ^ 2 := by
        have hle : η / 2 ≤ ‖s‖ / 2 := by
          change η < ‖s‖ at h
          linarith
        have hs₁ : 0 ≤ Real.sin (η / 2) := Real.sin_nonneg_of_nonneg_of_le_pi
          (by positivity) (by linarith [Real.pi_pos])
        have hs₂ : 0 ≤ Real.sin (‖s‖ / 2) := Real.sin_nonneg_of_nonneg_of_le_pi
          (by positivity) (by linarith [Real.pi_pos])
        apply (sq_le_sq₀ hs₁ hs₂).mpr
        exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hs hle
      have hmul := mul_le_mul hvar hsine (sq_nonneg (Real.sin (η / 2))) hw
      dsimp only [c]
      nlinarith only [hmul]
    · rw [show weight e = 1 by simp [weight, h]]
      exact Real.exp_le_one_iff.mpr (by
        nlinarith only [mul_nonneg hw (sq_nonneg (Real.sin (‖s‖ / 2)))])
  calc
    _ = ∏ e ∈ A, ‖phaseBernoulliFactor (q e) (t e.val.1 + t e.val.2)‖ :=
      degreeFourier_norm_eq_phase_product A q d t
    _ ≤ ∏ e ∈ A, weight e := Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) hpt
    _ = _ := by
      change (∏ e ∈ A, weight e) = Real.exp (-c * ((A.filter P).card : ℝ))
      rw [← Finset.prod_filter_mul_prod_filter_not A P weight]
      have hgood : (∏ e ∈ A.filter (fun e ↦ ¬ P e), weight e) = 1 := by
        apply Finset.prod_eq_one
        intro e he
        simp [weight, (Finset.mem_filter.mp he).2]
      have hbad : (∏ e ∈ A.filter P, weight e) = Real.exp (-c) ^ (A.filter P).card := by
        rw [← Finset.prod_const]
        apply Finset.prod_congr rfl
        intro e he
        simp [weight, (Finset.mem_filter.mp he).2]
      rw [hgood, hbad, mul_one, ← Real.exp_nat_mul]
      congr 1
      ring

/-- The large bad-edge region contributes at most the same exponential
bound to the normalized Fourier integral. -/
theorem integral_degreeFourier_many_bad_le (A : Finset (Edge α))
    (q : Edge α → Set.Icc (0 : ℝ) 1) (d : α → ℤ) (m : ℕ)
    {η lower : ℝ} (hη : 0 ≤ η) (hlower : 0 ≤ lower)
    (hq : ∀ e ∈ A, lower ≤ (q e : ℝ) * (1 - q e)) :
    (∫ t in {t : α → PhaseCircle |
      m ≤ (A.filter fun e ↦ η < ‖t e.val.1 + t e.val.2‖).card},
      ‖degreeFourier A q d t‖ ∂(phaseLaw : Measure (α → PhaseCircle))) ≤
        Real.exp (-(2 * lower * Real.sin (η / 2) ^ 2) * m) := by
  classical
  let c := 2 * lower * Real.sin (η / 2) ^ 2
  let ηbad (e : Edge α) (t : α → PhaseCircle) : Prop := η < ‖t e.val.1 + t e.val.2‖
  let B (t : α → PhaseCircle) := (A.filter (fun e ↦ ηbad e t)).card
  let T : Set (α → PhaseCircle) := {t | m ≤ B t}
  have hB : Measurable B := by
    have hpoint (e : Edge α) : MeasurableSet {t : α → PhaseCircle | ηbad e t} :=
      measurableSet_lt measurable_const
        (((measurable_pi_apply e.val.1).add (measurable_pi_apply e.val.2)).norm)
    have hpower : Measurable (fun t : α → PhaseCircle ↦ ∑ e ∈ A, if ηbad e t then (1 : ℕ) else 0) :=
      Finset.measurable_sum _ (fun e _ ↦ Measurable.ite (hpoint e) measurable_const measurable_const)
    have heq (t : α → PhaseCircle) :
        (∑ e ∈ A, if ηbad e t then (1 : ℕ) else 0) = B t := by
      simp [B]
    have he : (fun t : α → PhaseCircle ↦ ∑ e ∈ A, if ηbad e t then (1 : ℕ) else 0) = B :=
      funext heq
    rwa [he] at hpower
  have hT : MeasurableSet T := measurableSet_le measurable_const hB
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have : IsProbabilityMeasure (phaseLaw : Measure (α → PhaseCircle)) := by
    unfold phaseLaw
    infer_instance
  change (∫ t in T, ‖degreeFourier A q d t‖ ∂phaseLaw) ≤ _
  calc
    _ ≤ ∫ _ in T, Real.exp (-c * m) ∂phaseLaw := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun _ ↦ norm_nonneg _)) (integrable_const _)
      filter_upwards [ae_restrict_mem hT] with t ht
      refine (degreeFourier_norm_le_torus_bad_count A q d t hη hlower hq).trans ?_
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hc)
      change m ≤ B t at ht
      exact_mod_cast ht
    _ ≤ _ := by
      rw [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
      change phaseLaw.real T * Real.exp (-c * m) ≤ _
      exact mul_le_of_le_one_left (Real.exp_nonneg _) (measureReal_le_one (μ := phaseLaw))

end BoundedEdgeRegularSubgraphs
