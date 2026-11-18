module

public import BoundedEdgeRegularSubgraphs.FourierReplacement
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic

/-!
# Replacement measure and the fibre integral comparison
-/

public section

open MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- A circle ball of radius at most π has normalized Haar measure (r/π). -/
theorem phase_closedBall_measure (b : PhaseCircle) {r : ℝ}
    (hr : 0 ≤ r) (hr' : r ≤ Real.pi) :
    (AddCircle.haarAddCircle : Measure PhaseCircle).real (Metric.closedBall b r) = r / Real.pi := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have h := congrArg ENNReal.toReal (AddCircle.volume_closedBall (T := 2 * Real.pi) (x := b) r)
  rw [AddCircle.volume_eq_smul_haarAddCircle, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi), min_eq_right (by linarith),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * r)] at h
  change (2 * Real.pi) * (AddCircle.haarAddCircle : Measure PhaseCircle).real (Metric.closedBall b r) =
    2 * r at h
  apply (eq_div_iff hπ.ne').mpr
  nlinarith only [h]

/-- Excluding finitely many antipode windows leaves an explicit lower bound
on the measure of the permitted replacement phases. -/
theorem phase_replacement_measure_lower {ι : Type*} (A : Finset ι) (b : PhaseCircle)
    (centres : ι → PhaseCircle) {η r : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ Real.pi) (hr : 0 ≤ r) (hr' : r ≤ Real.pi) :
    (η - (A.card : ℝ) * r) / Real.pi ≤
      (AddCircle.haarAddCircle : Measure PhaseCircle).real
        (Metric.closedBall b η \ ⋃ i ∈ A, Metric.closedBall (centres i) r) := by
  let μ : Measure PhaseCircle := AddCircle.haarAddCircle
  let U : Set PhaseCircle := ⋃ i ∈ A, Metric.closedBall (centres i) r
  have hU : μ.real U ≤ (A.card : ℝ) * (r / Real.pi) := by
    refine (measureReal_biUnion_finset_le A _).trans_eq ?_
    change (∑ i ∈ A, (AddCircle.haarAddCircle : Measure PhaseCircle).real
      (Metric.closedBall (centres i) r)) = _
    simp only [phase_closedBall_measure (centres _) hr hr', Finset.sum_const, nsmul_eq_mul]
  have hB : μ.real (Metric.closedBall b η) = η / Real.pi := phase_closedBall_measure b hη hη'
  calc
    _ = η / Real.pi - (A.card : ℝ) * (r / Real.pi) := by ring
    _ ≤ μ.real (Metric.closedBall b η) - μ.real U := by rw [hB]; linarith
    _ ≤ _ := le_measureReal_sdiff (measure_ne_top _ _)

/-- Integrating a pointwise comparison with every permitted replacement
gives the fibre estimate used in Lemma B.1. -/
theorem integral_fibre_le_of_replacement {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Integrable f μ)
    (h₀ : ∀ x, 0 ≤ f x) (X Y : Set Ω) (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hy : 0 < μ.real Y) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x ∈ X, ∀ y ∈ Y, f x ≤ c * f y) :
    (∫ x in X, f x ∂μ) ≤ (c / μ.real Y) * ∫ y, f y ∂μ := by
  have hYbound : (∫ y in Y, f y ∂μ) ≤ ∫ y, f y ∂μ :=
    setIntegral_le_integral hf (ae_of_all _ h₀)
  have hF : ∀ x ∈ X, f x ≤ (c / μ.real Y) * ∫ y, f y ∂μ := by
    intro x hx
    have hcomp : (∫ _ in Y, f x ∂μ) ≤ ∫ y in Y, c * f y ∂μ := by
      apply integral_mono_ae (integrable_const _) (hf.integrableOn.const_mul _)
      filter_upwards [ae_restrict_mem hY] with y hy'
      exact h x hx y hy'
    rw [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ,
      ← measureReal_def, integral_const_mul, mul_comm (μ.real Y)] at hcomp
    have hstep := hcomp.trans (mul_le_mul_of_nonneg_left hYbound hc)
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hy).mpr hstep
  let C : ℝ := (c / μ.real Y) * ∫ y, f y ∂μ
  have hC : 0 ≤ C := mul_nonneg (div_nonneg hc hy.le) (integral_nonneg h₀)
  calc
    _ ≤ ∫ _ in X, C ∂μ := by
      apply integral_mono_ae hf.integrableOn (integrable_const _)
      filter_upwards [ae_restrict_mem hX] with x hx
      exact hF x hx
    _ ≤ _ := by
      rw [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
      change μ.real X * C ≤ C
      exact mul_le_of_le_one_left hC measureReal_le_one

end BoundedEdgeRegularSubgraphs
