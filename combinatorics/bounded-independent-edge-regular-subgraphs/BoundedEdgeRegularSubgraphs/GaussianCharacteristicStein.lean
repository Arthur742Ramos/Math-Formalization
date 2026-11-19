module

public import BoundedEdgeRegularSubgraphs.GaussianCharacteristicDerivative
public import BoundedEdgeRegularSubgraphs.GaussianCubicStein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# The cubic characteristic function and the Stein identity
-/

public section

open MeasureTheory Matrix MvPolynomial

namespace BoundedEdgeRegularSubgraphs

private theorem integrable_mul_realCharacter {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F H : X → ℝ} (hF : AEMeasurable F μ) (hH : Integrable H μ) (s : ℝ) :
    Integrable (fun x ↦ (H x : ℂ) * realCharacter s (F x)) μ := by
  have hM := ((continuous_realCharacter s).measurable.comp_aemeasurable hF).aestronglyMeasurable
  have hH' := (Complex.continuous_ofReal.measurable.comp_aemeasurable hH.aemeasurable).aestronglyMeasurable
  apply hH.abs.mono' (hH'.mul hM)
  exact ae_of_all _ (fun x ↦ by
    change ‖(H x : ℂ) * realCharacter s (F x)‖ ≤ |H x|
    rw [norm_mul, norm_realCharacter, mul_one, Complex.norm_real, Real.norm_eq_abs])

private theorem integral_mul_realCharacter_re {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F H : X → ℝ} (hF : AEMeasurable F μ) (hH : Integrable H μ) (s : ℝ) :
    (∫ x, (H x : ℂ) * realCharacter s (F x) ∂μ).re = ∫ x, H x * Real.cos (s * F x) ∂μ := by
  have h := (integral_re (integrable_mul_realCharacter hF hH s)).symm
  change (∫ x, (H x : ℂ) * realCharacter s (F x) ∂μ).re =
    ∫ x, ((H x : ℂ) * realCharacter s (F x)).re ∂μ at h
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    realCharacter, Complex.exp_ofReal_mul_I_re] using h

private theorem integral_mul_realCharacter_im {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F H : X → ℝ} (hF : AEMeasurable F μ) (hH : Integrable H μ) (s : ℝ) :
    (∫ x, (H x : ℂ) * realCharacter s (F x) ∂μ).im = ∫ x, H x * Real.sin (s * F x) ∂μ := by
  have h := (integral_im (integrable_mul_realCharacter hF hH s)).symm
  change (∫ x, (H x : ℂ) * realCharacter s (F x) ∂μ).im =
    ∫ x, ((H x : ℂ) * realCharacter s (F x)).im ∂μ at h
  simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    realCharacter, Complex.exp_ofReal_mul_I_im] using h

/-- The complex test-function identity for the cubic and its gradient product. -/
theorem integral_cubic_mul_realCharacter_eq {n : ℕ} {ι : Type*}
    (A : Finset ι) (a : ι → ℝ) (v : ι → Fin (n + 1) → ℝ) (s : ℝ) :
    let F := fun x ↦ eval x (gaussianCubicPolynomial A a v)
    let Γ := fun x ↦ eval x (gaussianGradientProduct (gaussianCubicPolynomial A a v)
      (gaussianCubicAuxiliary A a v))
    let γ := standardGaussianProduct (n + 1)
    (∫ x, (F x : ℂ) * realCharacter s (F x) ∂γ) =
      ((s : ℂ) * Complex.I) * ∫ x, (Γ x : ℂ) * realCharacter s (F x) ∂γ := by
  let f := gaussianCubicPolynomial A a v
  let g := gaussianCubicAuxiliary A a v
  let F (x : Fin (n + 1) → ℝ) := eval x f
  let Γ (x : Fin (n + 1) → ℝ) := eval x (gaussianGradientProduct f g)
  let γ := standardGaussianProduct (n + 1)
  have hf : Integrable F γ := integrable_eval_standardGaussianProduct f
  have hΓ : Integrable Γ γ := integrable_eval_standardGaussianProduct _
  have hL (x : Fin (n + 1) → ℝ) : eval x (gaussianGeneratorNeg g) = F x :=
    eval_gaussianGeneratorNeg_cubicAuxiliary A a v x
  have hder (x : ℝ) : HasDerivAt (fun t ↦ s * t) s x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul s
  have hCos := integral_gaussianGeneratorNeg_mul_test_eq f g
    (fun x ↦ Real.cos (s * x)) (fun x ↦ -s * Real.sin (s * x))
    (fun x ↦ by convert (hder x).cos using 1; ring)
    (by fun_prop) (fun x ↦ Real.abs_cos_le_one (s * x))
    (fun x ↦ by rw [abs_mul, abs_neg]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))
  have hSin := integral_gaussianGeneratorNeg_mul_test_eq f g
    (fun x ↦ Real.sin (s * x)) (fun x ↦ s * Real.cos (s * x))
    (fun x ↦ by convert (hder x).sin using 1; ring)
    (by fun_prop) (fun x ↦ Real.abs_sin_le_one (s * x))
    (fun x ↦ by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
  simp_rw [hL] at hCos hSin
  have hCos' : (∫ x, F x * Real.cos (s * F x) ∂γ) = -s * ∫ x, Γ x * Real.sin (s * F x) ∂γ := by
    change (∫ x, Real.cos (s * F x) * F x ∂γ) = ∫ x, (-s * Real.sin (s * F x)) * Γ x ∂γ at hCos
    simp_rw [mul_comm (Real.cos _) (F _), mul_assoc, mul_comm (Real.sin _) (Γ _), integral_const_mul] at hCos
    exact hCos
  have hSin' : (∫ x, F x * Real.sin (s * F x) ∂γ) = s * ∫ x, Γ x * Real.cos (s * F x) ∂γ := by
    change (∫ x, Real.sin (s * F x) * F x ∂γ) = ∫ x, (s * Real.cos (s * F x)) * Γ x ∂γ at hSin
    simp_rw [mul_comm (Real.sin _) (F _), mul_assoc, mul_comm (Real.cos _) (Γ _), integral_const_mul] at hSin
    exact hSin
  change (∫ x, (F x : ℂ) * realCharacter s (F x) ∂γ) =
    ((s : ℂ) * Complex.I) * ∫ x, (Γ x : ℂ) * realCharacter s (F x) ∂γ
  apply Complex.ext
  · rw [integral_mul_realCharacter_re hf.aemeasurable hf, Complex.mul_re,
      integral_mul_realCharacter_im hf.aemeasurable hΓ]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, mul_one, zero_sub, ← neg_mul]
    exact hCos'
  · rw [integral_mul_realCharacter_im hf.aemeasurable hf, Complex.mul_im,
      integral_mul_realCharacter_re hf.aemeasurable hΓ]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one]
    exact hSin'

end BoundedEdgeRegularSubgraphs
