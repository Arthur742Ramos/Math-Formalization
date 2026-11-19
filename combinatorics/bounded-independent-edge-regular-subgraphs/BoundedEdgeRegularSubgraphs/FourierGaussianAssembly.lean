module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic

/-!
# Combining the phase, quartic weight and small remainder
-/

public section

open MeasureTheory

namespace BoundedEdgeRegularSubgraphs

/-- The quantitative triangle inequality used to assemble (A.3).
The phase has modulus one, the weight includes the box indicator,
and the uniform remainder appears in the exponential. -/
theorem norm_integral_phase_weight_remainder_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u r : Ω → ℂ) (w : Ω → ℝ)
    (hu : AEStronglyMeasurable u μ) (hr : AEStronglyMeasurable r μ)
    (hw : Integrable w μ) (hw₀ : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hun : ∀ᵐ x ∂μ, ‖u x‖ = 1)
    {ε : ℝ} (hε : ε ≤ 1) (hrn : ∀ᵐ x ∂μ, ‖r x‖ ≤ ε) (c : ℝ) (z : ℂ) :
    ‖(∫ x, u x * (w x : ℂ) * Complex.exp (r x) ∂μ) - (c : ℂ) * z‖ ≤
      2 * ε * (∫ x, w x ∂μ) + (∫ x, |w x - c| ∂μ) +
        |c| * ‖(∫ x, u x ∂μ) - z‖ := by
  let v (x : Ω) := u x * (w x : ℂ)
  let W (x : Ω) := v x * Complex.exp (r x)
  let C (x : Ω) := (c : ℂ) * u x
  have hiU : Integrable u μ :=
    Integrable.of_bound hu 1 (hun.mono fun _ h ↦ h.le)
  have hiC : Integrable C μ := hiU.const_mul _
  have hiV : Integrable v μ := by
    have hm : AEStronglyMeasurable (fun x ↦ (w x : ℂ)) μ :=
      (Complex.continuous_ofReal.measurable.comp_aemeasurable hw.aemeasurable).aestronglyMeasurable
    refine hw.mono' (hu.mul hm) ?_
    filter_upwards [hun, hw₀] with x hx hwx
    simp only [v, norm_mul, hx, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwx, le_rfl]
  have hiW : Integrable W μ := by
    have hC : AEStronglyMeasurable (fun x ↦ Complex.exp (r x)) μ :=
      (Complex.continuous_exp.measurable.comp_aemeasurable hr.aemeasurable).aestronglyMeasurable
    refine (hw.mul_const (Real.exp 1)).mono' (hiV.1.mul hC) ?_
    filter_upwards [hun, hw₀, hrn] with x hx hwx hrx
    simp only [W, v, norm_mul, hx, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwx]
    exact mul_le_mul_of_nonneg_left ((Complex.norm_exp_le_exp_norm _).trans
      (Real.exp_le_exp.mpr (hrx.trans hε))) hwx
  have hWV : ‖(∫ x, W x ∂μ) - ∫ x, v x ∂μ‖ ≤ 2 * ε * ∫ x, w x ∂μ := by
    rw [← integral_sub hiW hiV, ← integral_const_mul]
    apply norm_integral_le_of_norm_le (hw.const_mul _)
    filter_upwards [hun, hw₀, hrn] with x hx hwx hrx
    change ‖v x * Complex.exp (r x) - v x‖ ≤ _
    rw [show v x * Complex.exp (r x) - v x = v x * (Complex.exp (r x) - 1) by ring]
    simp only [v, norm_mul, hx, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwx]
    rw [mul_comm (2 * ε) (w x)]
    exact mul_le_mul_of_nonneg_left ((Complex.norm_exp_sub_one_le (hrx.trans hε)).trans
      (mul_le_mul_of_nonneg_left hrx (by norm_num))) hwx
  have hVC : ‖(∫ x, v x ∂μ) - ∫ x, C x ∂μ‖ ≤ ∫ x, |w x - c| ∂μ := by
    rw [← integral_sub hiV hiC]
    apply norm_integral_le_of_norm_le ((hw.sub (integrable_const c)).abs)
    filter_upwards [hun] with x hx
    change ‖u x * (w x : ℂ) - (c : ℂ) * u x‖ ≤ _
    rw [show u x * (w x : ℂ) - (c : ℂ) * u x = u x * (((w x - c : ℝ) : ℂ)) by
      push_cast; ring, norm_mul, hx, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact le_rfl
  have hCZ : ‖(∫ x, C x ∂μ) - (c : ℂ) * z‖ = |c| * ‖(∫ x, u x ∂μ) - z‖ := by
    change ‖(∫ x, (c : ℂ) * u x ∂μ) - (c : ℂ) * z‖ = _
    rw [integral_const_mul, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  let a₁ := ∫ x, W x ∂μ
  let a₂ := ∫ x, v x ∂μ
  let a₃ := ∫ x, C x ∂μ
  let a₄ := (c : ℂ) * z
  have h₁ := dist_triangle a₁ a₂ a₄
  have h₂ := dist_triangle a₂ a₃ a₄
  simp only [dist_eq_norm] at h₁ h₂
  change ‖a₁ - a₄‖ ≤ _
  change ‖a₁ - a₂‖ ≤ _ at hWV
  change ‖a₂ - a₃‖ ≤ _ at hVC
  change ‖a₃ - a₄‖ = _ at hCZ
  linarith only [h₁, h₂, hWV, hVC, hCZ]

end BoundedEdgeRegularSubgraphs
