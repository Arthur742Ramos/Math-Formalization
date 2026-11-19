module

public import BoundedEdgeRegularSubgraphs.FourierGaussianError
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Gaussian representation of the small-box Fourier modulus
-/

public section

open MeasureTheory Matrix Set
open scoped BigOperators MatrixOrder

namespace BoundedEdgeRegularSubgraphs

/-- The modulus has its exact Gaussian representation for all available
edge sets, including residual arrays. -/
theorem integral_norm_degreeFourier_smallBox_eq_gaussian {n : ℕ}
    (A : Finset (Edge (Fin n))) (q : Edge (Fin n) → Icc (0 : ℝ) 1) (d : Fin n → ℤ)
    (hQ : (degreeCovariance A q).PosDef) {r : ℝ} (hr : 2 * r ≤ 1 / 4) :
    let Q := degreeCovariance A q
    let B := (CFC.sqrt Q)⁻¹
    let U := phaseGaussianBox Q r
    (∫ t in phaseBox (0 : PhaseCircle) r, ‖degreeFourier A q d t‖ ∂phaseLaw) =
      phaseGaussianScale Q *
        ∫ x, U.indicator (fun x ↦ Real.exp (phaseGaussianQuartic A q x +
          (degreeFourierLocalError A q (B *ᵥ x)).re)) x ∂standardGaussianProduct n := by
  let Q := degreeCovariance A q
  let B := (CFC.sqrt Q)⁻¹
  let U := realPhaseBox (α := Fin n) r
  let V := phaseGaussianBox Q r
  let h := edgeQuartic A (fun e ↦ degreeQuarticCoefficient (q e))
  let W (t : Fin n → ℝ) := Real.exp (h t + (degreeFourierLocalError A q t).re)
  let P (t : Fin n → ℝ) (i : Fin n) := (t i : PhaseCircle)
  let L (t : Fin n → ℝ) := Real.exp (-(t ⬝ᵥ (Q *ᵥ t)) / 2)
  let s : ℝ := (2 * Real.pi) ^ n
  let Ξ := (Real.sqrt (2 * Real.pi)) ^ n / Real.sqrt Q.det
  have hs : 0 < s := by dsimp only [s]; positivity
  have hrπ : r < Real.pi := by linarith only [hr, Real.pi_gt_three]
  have hU : MeasurableSet U := by
    rw [show U = ⋂ i, {x : Fin n → ℝ | |x i| ≤ r} by ext x; simp [U, realPhaseBox]]
    exact MeasurableSet.iInter (fun i ↦ measurableSet_le
      (continuous_abs.measurable.comp (measurable_pi_apply i)) measurable_const)
  have hh : Continuous h := by
    unfold h edgeQuartic
    apply continuous_finsetSum
    intro e _
    fun_prop
  have hW : StronglyMeasurable W := (Real.continuous_exp.measurable.comp
    (hh.measurable.add (Complex.continuous_re.measurable.comp
      (measurable_degreeFourierLocalError A q)))).stronglyMeasurable
  have hpoint (t : Fin n → ℝ) (ht : t ∈ U) : ‖degreeFourier A q d (P t)‖ = L t * W t := by
    have hsmall (e : Edge (Fin n)) (_ : e ∈ A) : |t e.val.1 + t e.val.2| ≤ 1 / 4 :=
      (abs_add_le _ _).trans (by linarith only [ht e.val.1, ht e.val.2, hr])
    rw [norm_degreeFourier_eq_exp_local_expansion A q d t hsmall]
    change Real.exp (-(t ⬝ᵥ (Q *ᵥ t)) / 2 + h t + (degreeFourierLocalError A q t).re) = _
    rw [add_assoc, Real.exp_add]
  have hchart := integral_phaseBox_zero_eq_real (fun t ↦ ‖degreeFourier A q d t‖)
    (continuous_degreeFourier A q d).norm.stronglyMeasurable hrπ
  rw [Fintype.card_fin, smul_eq_mul] at hchart
  change (∫ t in U, ‖degreeFourier A q d (P t)‖) =
    s * ∫ t in phaseBox 0 r, ‖degreeFourier A q d t‖ ∂phaseLaw at hchart
  have hlocal : (∫ t in U, ‖degreeFourier A q d (P t)‖) = ∫ t, L t * U.indicator W t := by
    rw [← integral_indicator hU]
    apply integral_congr_ae
    exact ae_of_all _ (fun t ↦ by
      change U.indicator (fun z ↦ ‖degreeFourier A q d (P z)‖) t = L t * U.indicator W t
      by_cases ht : t ∈ U
      · rw [indicator_of_mem ht, indicator_of_mem ht, hpoint t ht]
      · rw [indicator_of_notMem ht, indicator_of_notMem ht, mul_zero])
  have hchange := integral_quadratic_smul_eq_gaussianProduct Q hQ (U.indicator W) (hW.indicator hU)
  change (∫ t, L t * U.indicator W t) = Ξ *
    ∫ x, U.indicator W (B *ᵥ x) ∂standardGaussianProduct n at hchange
  rw [hchart, hchange] at hlocal
  have hpre (x : Fin n → ℝ) :
      U.indicator W (B *ᵥ x) = V.indicator (W ∘ B.mulVec) x := by
    by_cases hx : x ∈ V
    · rw [indicator_of_mem (show B *ᵥ x ∈ U from hx), indicator_of_mem hx]
      rfl
    · rw [indicator_of_notMem (show B *ᵥ x ∉ U from hx), indicator_of_notMem hx]
  simp_rw [hpre] at hlocal
  change (∫ t in phaseBox 0 r, ‖degreeFourier A q d t‖ ∂phaseLaw) =
    Ξ / s * ∫ x, V.indicator (W ∘ B.mulVec) x ∂standardGaussianProduct n
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hs.ne').2
  simpa only [mul_comm s] using hlocal

end BoundedEdgeRegularSubgraphs
