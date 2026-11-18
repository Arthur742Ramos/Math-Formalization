module

public import BoundedEdgeRegularSubgraphs.FourierSmallBoxBound
public import BoundedEdgeRegularSubgraphs.GaussianCharacteristicDerivative
import BoundedEdgeRegularSubgraphs.MeanDrift
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Exact Gaussian representation of the centred small-box integral
-/

public section

open MeasureTheory Set Matrix
open scoped BigOperators MatrixOrder

namespace BoundedEdgeRegularSubgraphs

/-- The centred Fourier integral over the small box has the exact
Gaussian phase, quartic weight and Taylor error, with the correct scale. -/
theorem integral_degreeFourier_centered_smallBox_eq_gaussian {n : ℕ}
    (q : Edge (Fin n) → Icc (0 : ℝ) 1) (d : Fin n → ℤ)
    (hd : ∀ i, (d i : ℝ) = degreeSum (fun e ↦ (q e : ℝ)) i)
    (hQ : (degreeCovariance Finset.univ q).PosDef) {r : ℝ} (hr : 2 * r ≤ 1 / 4) :
    let Q := degreeCovariance Finset.univ q
    let B := (CFC.sqrt Q)⁻¹
    let F := edgeCubic Finset.univ (fun e ↦ degreeCubicCoefficient (q e))
    let H := edgeQuartic Finset.univ (fun e ↦ degreeQuarticCoefficient (q e))
    let U := {x : Fin n → ℝ | B *ᵥ x ∈ realPhaseBox (α := Fin n) r}
    let R := degreeFourierLocalError Finset.univ q
    (∫ t in phaseBox (0 : PhaseCircle) r, degreeFourier Finset.univ q d t ∂phaseLaw) =
      (phaseGaussianScale Q : ℂ) *
        ∫ x, U.indicator (fun x ↦ realCharacter 1 (F (B *ᵥ x)) *
          (Real.exp (H (B *ᵥ x)) : ℂ) * Complex.exp (R (B *ᵥ x))) x ∂standardGaussianProduct n := by
  let A : Finset (Edge (Fin n)) := Finset.univ
  let Q := degreeCovariance A q
  let B := (CFC.sqrt Q)⁻¹
  let F := edgeCubic A (fun e ↦ degreeCubicCoefficient (q e))
  let H := edgeQuartic A (fun e ↦ degreeQuarticCoefficient (q e))
  let R := degreeFourierLocalError A q
  let U := realPhaseBox (α := Fin n) r
  let P (t : Fin n → ℝ) (i : Fin n) := (t i : PhaseCircle)
  let W (t : Fin n → ℝ) := realCharacter 1 (F t) * (Real.exp (H t) : ℂ) * Complex.exp (R t)
  let L (t : Fin n → ℝ) := Real.exp (-(t ⬝ᵥ (Q *ᵥ t)) / 2)
  let s : ℝ := (2 * Real.pi) ^ n
  let Ξ := (Real.sqrt (2 * Real.pi)) ^ n / Real.sqrt Q.det
  have hs : 0 < s := by dsimp only [s]; positivity
  have hrπ : r < Real.pi := by linarith only [hr, Real.pi_gt_three]
  have hU : MeasurableSet U := by
    rw [show U = ⋂ i, {x : Fin n → ℝ | |x i| ≤ r} by ext x; simp [U, realPhaseBox]]
    exact MeasurableSet.iInter (fun i ↦ measurableSet_le
      (continuous_abs.measurable.comp (measurable_pi_apply i)) measurable_const)
  have hcontF : Continuous F := by
    unfold F edgeCubic
    apply continuous_finsetSum
    intro e _
    fun_prop
  have hcontH : Continuous H := by
    unfold H edgeQuartic
    apply continuous_finsetSum
    intro e _
    fun_prop
  have hW : StronglyMeasurable W :=
    (((continuous_realCharacter 1).comp hcontF).measurable.mul
      ((Complex.continuous_ofReal.comp Real.continuous_exp).comp hcontH).measurable).mul
      (Complex.continuous_exp.measurable.comp (measurable_degreeFourierLocalError A q))
      |>.stronglyMeasurable
  have hpoint (t : Fin n → ℝ) (ht : t ∈ U) : degreeFourier A q d (P t) = L t • W t := by
    have hsmall (e : Edge (Fin n)) (_ : e ∈ A) : |t e.val.1 + t e.val.2| ≤ 1 / 4 :=
      (abs_add_le _ _).trans (by linarith only [ht e.val.1, ht e.val.2, hr])
    have hlinear : (∑ e ∈ A, (q e : ℝ) * (t e.val.1 + t e.val.2)) -
        (∑ i, (d i : ℝ) * t i) = 0 := by
      simp_rw [hd, mul_comm (degreeSum _ _) (t _)]
      change (∑ e : Edge (Fin n), (q e : ℝ) * (t e.val.1 + t e.val.2)) -
        ∑ i, t i * degreeSum (fun e ↦ (q e : ℝ)) i = 0
      rw [weighted_degree_sum]
      have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Edge (Fin n)))) rfl
        (fun e _ ↦ mul_comm (q e : ℝ) (t e.val.1 + t e.val.2))
      rw [h, sub_self]
    rw [degreeFourier_eq_exp_local_expansion A q d t hsmall, hlinear, add_zero]
    change Complex.exp (((-(t ⬝ᵥ (Q *ᵥ t)) / 2 + H t : ℝ) : ℂ) +
      (F t : ℂ) * Complex.I + R t) = _
    simp only [W, L, realCharacter, one_mul, Complex.ofReal_add, Complex.exp_add,
      Complex.ofReal_exp, Complex.real_smul]
    ring
  have hchart := integral_phaseBox_zero_eq_real (degreeFourier A q d)
    (continuous_degreeFourier A q d).stronglyMeasurable hrπ
  rw [Fintype.card_fin] at hchart
  change (∫ t in U, degreeFourier A q d (P t)) =
    s • ∫ t in phaseBox 0 r, degreeFourier A q d t ∂phaseLaw at hchart
  have hlocal : (∫ t in U, degreeFourier A q d (P t)) = ∫ t, L t • U.indicator W t := by
    rw [← integral_indicator hU]
    apply integral_congr_ae
    exact ae_of_all _ (fun t ↦ by
      change U.indicator (fun z ↦ degreeFourier A q d (P z)) t = L t • U.indicator W t
      by_cases ht : t ∈ U
      · rw [indicator_of_mem ht, indicator_of_mem ht, hpoint t ht]
      · rw [indicator_of_notMem ht, indicator_of_notMem ht, smul_zero])
  have hchange := integral_quadratic_smul_eq_gaussianProduct Q hQ (U.indicator W) (hW.indicator hU)
  change (∫ t, L t • U.indicator W t) = Ξ •
    ∫ x, U.indicator W (B *ᵥ x) ∂standardGaussianProduct n at hchange
  rw [hchart, hchange] at hlocal
  have hpre (x : Fin n → ℝ) :
      U.indicator W (B *ᵥ x) = (B.mulVec ⁻¹' U).indicator (W ∘ B.mulVec) x := by
    by_cases h : B *ᵥ x ∈ U
    · rw [indicator_of_mem h, indicator_of_mem (show x ∈ B.mulVec ⁻¹' U from h)]
      rfl
    · rw [indicator_of_notMem h, indicator_of_notMem (show x ∉ B.mulVec ⁻¹' U from h)]
  change (∫ t in phaseBox 0 r, degreeFourier A q d t ∂phaseLaw) =
    ((Ξ / s : ℝ) : ℂ) * ∫ x, (B.mulVec ⁻¹' U).indicator (W ∘ B.mulVec) x ∂standardGaussianProduct n
  apply smul_right_injective ℂ (ne_of_gt hs)
  dsimp only
  simp_rw [hpre] at hlocal
  rw [hlocal]
  simp only [Complex.real_smul, Complex.ofReal_div]
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  field_simp [hsC]

end BoundedEdgeRegularSubgraphs
