module

public import BoundedEdgeRegularSubgraphs.GaussianParts
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-!
# Standard and scaled normal moment identities
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace BoundedEdgeRegularSubgraphs

private theorem gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * standardNormalKernel x := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, standardNormalKernel, neg_div]

/-- The normalized Gaussian integration-by-parts identity. -/
theorem integral_gaussianReal_zero_one_deriv (f f' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hi : Integrable (fun x ↦ standardNormalKernel x * f x))
    (hi' : Integrable (fun x ↦ standardNormalKernel x * f' x))
    (hxi : Integrable (fun x ↦ x * standardNormalKernel x * f x)) :
    (∫ x, f' x ∂gaussianReal 0 1) = ∫ x, x * f x ∂gaussianReal 0 1 := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [gaussianPDFReal_zero_one, smul_eq_mul, mul_assoc]
  have he (x : ℝ) :
      standardNormalKernel x * (x * f x) = x * standardNormalKernel x * f x := by ring
  simp only [he, integral_const_mul]
  rw [integral_standardNormalKernel_deriv f f' hf hi hi' hxi]

private theorem integrable_standardNormalKernel_mul {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal 0 1)) :
    Integrable (fun x ↦ standardNormalKernel x * f x) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1 : ℝ≥0) ≠ 0), gaussianPDF_def] at hf
  have h := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)).mp hf
  have hpdf (x : ℝ) : (gaussianPDF 0 1 x).toReal =
      (Real.sqrt (2 * Real.pi))⁻¹ * standardNormalKernel x := by
    rw [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
      gaussianPDFReal_zero_one]
  simp only [hpdf, smul_eq_mul, mul_assoc] at h
  have hh := h.const_mul (Real.sqrt (2 * Real.pi))
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  simpa only [← mul_assoc, mul_inv_cancel₀ hs, one_mul] using hh

/-- Standard Gaussian integration by parts with integrability expressed
under the Gaussian measure. -/
theorem integral_gaussianReal_deriv_eq_mul (f f' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hi : Integrable f (gaussianReal 0 1))
    (hi' : Integrable f' (gaussianReal 0 1))
    (hxi : Integrable (fun x ↦ x * f x) (gaussianReal 0 1)) :
    (∫ x, f' x ∂gaussianReal 0 1) = ∫ x, x * f x ∂gaussianReal 0 1 := by
  apply integral_gaussianReal_zero_one_deriv f f' hf
    (integrable_standardNormalKernel_mul hi) (integrable_standardNormalKernel_mul hi')
  simpa only [mul_left_comm (standardNormalKernel _) _, ← mul_assoc] using
    integrable_standardNormalKernel_mul hxi

theorem integral_standardNormalKernel :
    (∫ x : ℝ, standardNormalKernel x) = Real.sqrt (2 * Real.pi) := by
  have he (x : ℝ) : standardNormalKernel x = Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
    unfold standardNormalKernel
    congr 1
    ring
  simp_rw [he]
  rw [integral_gaussian]
  congr 1
  ring

/-- The even Gaussian moments are the odd double factorials times the Gaussian mass. -/
theorem integral_even_pow_standardNormalKernel (m : ℕ) :
    (∫ x : ℝ, x ^ (2 * m) * standardNormalKernel x) =
      (∏ j ∈ Finset.range m, (2 * (j : ℝ) + 1)) * Real.sqrt (2 * Real.pi) := by
  induction m with
  | zero => simp [integral_standardNormalKernel]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, integral_pow_add_two_standardNormalKernel,
      ih, Finset.prod_range_succ]
    push_cast
    ring

/-- The even moments of a standard normal variable. -/
theorem integral_even_pow_gaussianReal_zero_one (m : ℕ) :
    (∫ x : ℝ, x ^ (2 * m) ∂gaussianReal 0 1) =
      ∏ j ∈ Finset.range m, (2 * (j : ℝ) + 1) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [gaussianPDFReal_zero_one, smul_eq_mul, mul_assoc]
  have he (x : ℝ) : standardNormalKernel x * x ^ (2 * m) =
      x ^ (2 * m) * standardNormalKernel x := mul_comm _ _
  simp only [he, integral_const_mul, integral_even_pow_standardNormalKernel]
  field_simp

/-- The even Gaussian moments with general variance, including zero variance. -/
theorem integral_even_pow_gaussianReal (v : ℝ≥0) (m : ℕ) :
    (∫ x : ℝ, x ^ (2 * m) ∂gaussianReal 0 v) =
      (v : ℝ) ^ m * ∏ j ∈ Finset.range m, (2 * (j : ℝ) + 1) := by
  let c := Real.sqrt (v : ℝ)
  have hc : c ^ 2 = (v : ℝ) := Real.sq_sqrt v.property
  have hvar : (⟨c ^ 2, sq_nonneg c⟩ : ℝ≥0) = v := Subtype.ext hc
  have hmap : (gaussianReal 0 1).map (c * ·) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    exact congrArg (gaussianReal 0) hvar
  rw [← hmap, integral_map (by fun_prop) (by fun_prop)]
  simp only [mul_pow, integral_const_mul, integral_even_pow_gaussianReal_zero_one]
  rw [pow_mul, hc]

/-- The fourth moment of a centred Gaussian. -/
theorem integral_fourth_gaussianReal (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have h := integral_even_pow_gaussianReal v 2
  norm_num [Finset.prod_range_succ] at h
  linarith only [h]

/-- The eighth moment of a centred Gaussian. -/
theorem integral_eighth_gaussianReal (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 8 ∂gaussianReal 0 v) = 105 * (v : ℝ) ^ 4 := by
  have h := integral_even_pow_gaussianReal v 4
  norm_num [Finset.prod_range_succ] at h
  linarith only [h]

end BoundedEdgeRegularSubgraphs
