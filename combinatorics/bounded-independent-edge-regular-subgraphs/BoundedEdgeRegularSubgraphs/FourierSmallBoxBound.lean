module

public import BoundedEdgeRegularSubgraphs.FourierSmallBoxUpper
public import BoundedEdgeRegularSubgraphs.GaussianWhiteningBound
public import BoundedEdgeRegularSubgraphs.GaussianClippedExponential
import Mathlib.Tactic

/-!
# Bounding the small Fourier box from the covariance lower bound
-/

public section

open MeasureTheory Matrix Set
open scoped BigOperators MatrixOrder

namespace BoundedEdgeRegularSubgraphs

theorem phaseGaussianScale_eq {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) :
    phaseGaussianScale Q = 1 / ((Real.sqrt (2 * Real.pi)) ^ n * Real.sqrt Q.det) := by
  unfold phaseGaussianScale
  have hx : (Real.sqrt (2 * Real.pi) ^ n) ^ 2 = (2 * Real.pi) ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (by positivity)]
  rw [← hx]
  have hSqrt : 0 < Real.sqrt Q.det := Real.sqrt_pos.mpr hQ.det_pos
  field_simp [hSqrt.ne', (Real.sqrt_pos.mpr (by positivity : 0 < 2 * Real.pi)).ne']

/-- A single small Fourier box has the Gaussian-scale bound for every
degree vector. The two extra terms give its quartic mean and concentration costs. -/
theorem integral_degreeFourier_smallBox_le_exp_of_covariance_lower {n : ℕ} (hn : 0 < n)
    (A : Finset (Edge (Fin n))) (q : Edge (Fin n) → Icc (0 : ℝ) 1) (d : Fin n → ℤ)
    (hQ : (degreeCovariance A q).PosDef) {lower r ε : ℝ} (hlower : 0 < lower)
    (hquad : ∀ x : Fin n → ℝ, lower * ∑ i, x i ^ 2 ≤ x ⬝ᵥ (degreeCovariance A q *ᵥ x))
    (hr : 0 ≤ r) (hr' : 2 * r ≤ 1 / 4)
    (hε : ∀ x ∈ realPhaseBox (α := Fin n) r, ‖degreeFourierLocalError A q x‖ ≤ ε) :
    let Q := degreeCovariance A q
    let K := (1 / 96 : ℝ)
    let κ := 4 * (2 * r) ^ 3 * K * ((n : ℝ) - 1) * Real.sqrt n * Real.sqrt lower⁻¹
    (∫ t in phaseBox (0 : PhaseCircle) r, ‖degreeFourier A q d t‖ ∂phaseLaw) ≤
      Real.exp (ε + 24 * K * ((n : ℝ) - 1) * n * lower⁻¹ ^ 2 + κ ^ 2 / 2) * phaseGaussianScale Q := by
  let Q := degreeCovariance A q
  let B := (CFC.sqrt Q)⁻¹
  let b := fun e ↦ degreeQuarticCoefficient (q e)
  let K := (1 / 96 : ℝ)
  let κ := 4 * (2 * r) ^ 3 * K * ((n : ℝ) - 1) * Real.sqrt n * Real.sqrt lower⁻¹
  have hb (e : Edge (Fin n)) (_ : e ∈ A) : |b e| ≤ K := abs_degreeQuarticCoefficient_le _
  have hscale : 0 ≤ phaseGaussianScale Q := by
    rw [phaseGaussianScale_eq Q hQ]
    exact div_nonneg zero_le_one (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (Real.sqrt_nonneg _))
  obtain ⟨hB, hD⟩ := gaussian_inverse_sqrt_bounds Q hQ hlower hquad
  have hnorm (v : Fin n → ℝ) : (∑ i, (B *ᵥ v) i ^ 2) ≤ (Real.sqrt lower⁻¹) ^ 2 * ∑ i, v i ^ 2 := by
    rw [Real.sq_sqrt (inv_nonneg.mpr hlower.le)]
    exact hB v
  have hW := integral_exp_clipped_edgeQuartic_le hn A b
    (by norm_num [K]) hr (Real.sqrt_nonneg lower⁻¹) hb B hnorm hD
  have h := integral_degreeFourier_smallBox_le_clipped_exp A q d hQ hr hr' hε
  refine h.trans ((mul_le_mul_of_nonneg_left hW (mul_nonneg (Real.exp_nonneg _) hscale)).trans_eq ?_)
  let z := 24 * K * ((n : ℝ) - 1) * n * lower⁻¹ ^ 2
  change Real.exp ε * phaseGaussianScale Q *
    Real.exp (z + κ ^ 2 / 2) = Real.exp (ε + z + κ ^ 2 / 2) * phaseGaussianScale Q
  rw [add_assoc ε, Real.exp_add ε]
  ring

end BoundedEdgeRegularSubgraphs
