module

public import BoundedEdgeRegularSubgraphs.FourierModulusGaussian
public import BoundedEdgeRegularSubgraphs.GaussianQuarticUniform
public import BoundedEdgeRegularSubgraphs.FourierUniformBoxCost
import Mathlib.Tactic

/-!
# Uniform small-box expansion of the Fourier modulus
-/

public section

open Filter MeasureTheory Matrix Set
open scoped BigOperators MatrixOrder

namespace BoundedEdgeRegularSubgraphs

private theorem norm_exp_real_sub_one_le {R : ℂ} {η : ℝ} (hη : η ≤ 1) (hR : ‖R‖ ≤ η) :
    |Real.exp R.re - 1| ≤ 2 * η := by
  have hr : ‖R.re‖ ≤ η := by rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm R).trans hR
  have h := Complex.norm_exp_sub_one_le
    (show ‖(R.re : ℂ)‖ ≤ 1 by rw [Complex.norm_real]; exact hr.trans hη)
  rw [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_real] at h
  exact h.trans (mul_le_mul_of_nonneg_left hr (by norm_num))

/-- The second expansion in (A.3), uniform in the matrix lower bound,
the available edges and the target vector, in normalized Haar measure. -/
theorem eventually_smallBox_fourier_modulus_sub_le_uniform {a ε : ℝ}
    (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (A : Finset (Edge (Fin n)))
      (q : Edge (Fin n) → Icc (0 : ℝ) 1) (d : Fin n → ℤ),
      (degreeCovariance A q).PosDef →
      (∀ x : Fin n → ℝ, a * (n : ℝ) * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (degreeCovariance A q *ᵥ x)) →
      let Ξ := phaseGaussianScale (degreeCovariance A q)
      let ν := phaseGaussianQuarticMean A q
      |(∫ t in phaseBox (0 : PhaseCircle) (fourierBoxRadius n), ‖degreeFourier A q d t‖ ∂phaseLaw) -
        Ξ * Real.exp ν| ≤ ε * Ξ := by
  obtain ⟨M, hM, h₄⟩ := eventually_gaussian_quartic_box_weight_sub_le
    (a := a⁻¹) (K := 1 / 96) (by positivity) (by norm_num)
  let z := min 1 (ε / (3 * (Real.exp M + 1)))
  have hz₀ : 0 < z := lt_min zero_lt_one (by positivity)
  have hz₁ : z ≤ 1 := min_le_left _ _
  filter_upwards [h₄ z hz₀, eventually_degreeFourierLocalError_le hz₀,
    eventually_ge_atTop (1 : ℕ)] with n h₄' hr hn
  intro A q d hQ hQuad
  let Q := degreeCovariance A q
  let B := (CFC.sqrt Q)⁻¹
  let γ := standardGaussianProduct n
  let r := fourierBoxRadius n
  let U := phaseGaussianBox Q r
  let H := phaseGaussianQuartic A q
  let ν := phaseGaussianQuarticMean A q
  let R (x : Fin n → ℝ) := (degreeFourierLocalError A q (B *ᵥ x)).re
  let w (x : Fin n → ℝ) := U.indicator (fun x ↦ Real.exp (H x)) x
  let W (x : Fin n → ℝ) := U.indicator (fun x ↦ Real.exp (H x + R x)) x
  let Ξ := phaseGaussianScale Q
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hB, hRows⟩ := gaussian_inverse_sqrt_bounds Q hQ (mul_pos ha hn₀) hQuad
  have he : (a * (n : ℝ))⁻¹ = a⁻¹ / (n : ℝ) := by field_simp [ha.ne', hn₀.ne']
  simp only [he] at hB hRows
  obtain ⟨hν, hwError⟩ := h₄' A (fun e ↦ degreeQuarticCoefficient (q e)) B
    (fun e _ ↦ abs_degreeQuarticCoefficient_le (q e)) hRows hB
  have hU : MeasurableSet U := measurableSet_phaseGaussianBox Q r
  have hBcont (i : Fin n) : Continuous (fun x : Fin n → ℝ ↦ (B *ᵥ x) i) := by
    change Continuous (fun x : Fin n → ℝ ↦ ∑ j, B i j * x j)
    exact continuous_finsetSum _ (fun j _ ↦ continuous_const.mul (continuous_apply j))
  have hH : Continuous H := by
    change Continuous (fun x : Fin n → ℝ ↦
      ∑ e ∈ A, degreeQuarticCoefficient (q e) * ((B *ᵥ x) e.val.1 + (B *ᵥ x) e.val.2) ^ 4)
    exact continuous_finsetSum _ (fun e _ ↦ continuous_const.mul (((hBcont _).add (hBcont _)).pow 4))
  have hR : Measurable R := Complex.continuous_re.measurable.comp
    ((measurable_degreeFourierLocalError A q).comp
      (measurable_pi_iff.mpr (fun i ↦ (hBcont i).measurable)))
  have hw₀ (x : Fin n → ℝ) : 0 ≤ w x := by
    by_cases hx : x ∈ U
    · unfold w; rw [indicator_of_mem hx]; positivity
    · unfold w; rw [indicator_of_notMem hx]
  have hw : Integrable w γ := by
    let b₀ := (A.card : ℝ) * ((1 / 96) * (2 * r) ^ 4)
    apply Integrable.of_bound ((Real.continuous_exp.comp hH).measurable.indicator hU).aestronglyMeasurable
      (Real.exp b₀)
    refine ae_of_all _ (fun x ↦ ?_)
    change ‖w x‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (hw₀ x)]
    by_cases hx : x ∈ U
    · have hclip : (fun i ↦ clipRadius r ((B *ᵥ x) i)) = B *ᵥ x :=
        funext (fun i ↦ clipRadius_eq_of_abs_le (hx i))
      unfold w
      rw [indicator_of_mem hx]
      apply Real.exp_le_exp.mpr
      refine (le_abs_self (H x)).trans ?_
      change |edgeQuartic A (fun e ↦ degreeQuarticCoefficient (q e)) (B *ᵥ x)| ≤ b₀
      rw [← hclip]
      exact abs_edgeQuartic_clip_le A _ (by norm_num) hr.1 (fun e _ ↦ abs_degreeQuarticCoefficient_le _) _
    · unfold w; rw [indicator_of_notMem hx]; positivity
  have hdiff (x : Fin n → ℝ) : |W x - w x| ≤ 2 * z * w x := by
    unfold W w
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx, indicator_of_mem hx, Real.exp_add, ← mul_sub_one,
        abs_mul, abs_of_nonneg (Real.exp_nonneg _), mul_comm (2 * z)]
      exact mul_le_mul_of_nonneg_left
        (norm_exp_real_sub_one_le hz₁ (hr.2.2 A q (B *ᵥ x) hx)) (Real.exp_nonneg _)
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, sub_zero, abs_zero, mul_zero]
  have hWi : Integrable W γ := by
    have hint : Integrable (fun x ↦ W x - w x) γ := by
      have hm := ((Real.continuous_exp.measurable.comp (hH.measurable.add hR)).indicator hU).sub
        ((Real.continuous_exp.comp hH).measurable.indicator hU)
      exact (hw.const_mul (2 * z)).mono' hm.aestronglyMeasurable (ae_of_all _ (fun x ↦ by
        rw [Real.norm_eq_abs]; exact hdiff x))
    have he : (fun x ↦ W x - w x) + w = W := funext (fun x ↦ sub_add_cancel (W x) (w x))
    rw [← he]
    exact hint.add hw
  have hWeight : (∫ x, |w x - Real.exp ν| ∂γ) ≤ z := hwError
  have hnear : |(∫ x, w x ∂γ) - Real.exp ν| ≤ z := by
    rw [← show (∫ x, Real.exp ν ∂γ) = Real.exp ν by rw [integral_const, probReal_univ, one_smul],
      ← integral_sub hw (integrable_const _), ← Real.norm_eq_abs]
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (fun x ↦ w x - Real.exp ν)).trans hWeight
  have hExp : Real.exp ν ≤ Real.exp M := Real.exp_le_exp.mpr ((le_abs_self ν).trans hν)
  have hm : (∫ x, w x ∂γ) ≤ Real.exp M + z := by linarith only [(abs_le.mp hnear).2, hExp]
  have hRerr : |(∫ x, W x ∂γ) - ∫ x, w x ∂γ| ≤ 2 * z * (∫ x, w x ∂γ) := by
    rw [← integral_sub hWi hw, ← integral_const_mul, ← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le (hw.const_mul _) (ae_of_all _ (fun x ↦ by
      rw [Real.norm_eq_abs]; exact hdiff x))
  have hFinal : |(∫ x, W x ∂γ) - Real.exp ν| ≤ ε := by
    have hh := abs_add_le ((∫ x, W x ∂γ) - ∫ x, w x ∂γ) ((∫ x, w x ∂γ) - Real.exp ν)
    rw [sub_add_sub_cancel] at hh
    have hs := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * z by positivity)
    have hsz := mul_le_mul_of_nonneg_left hz₁ (show 0 ≤ 2 * z by positivity)
    have hzε := (le_div_iff₀ (show 0 < 3 * (Real.exp M + 1) by positivity)).mp
      (show z ≤ ε / (3 * (Real.exp M + 1)) from min_le_right _ _)
    nlinarith only [hh, hRerr, hnear, hs, hsz, hzε, mul_nonneg hz₀.le (Real.exp_nonneg M)]
  have hΞ : 0 ≤ Ξ := by dsimp only [Ξ]; rw [phaseGaussianScale_eq Q hQ]; positivity
  change |(∫ t in phaseBox (0 : PhaseCircle) r, ‖degreeFourier A q d t‖ ∂phaseLaw) -
    Ξ * Real.exp ν| ≤ ε * Ξ
  rw [integral_norm_degreeFourier_smallBox_eq_gaussian A q d hQ hr.2.1]
  change |Ξ * (∫ x, W x ∂γ) - Ξ * Real.exp ν| ≤ ε * Ξ
  rw [← mul_sub, abs_mul, abs_of_nonneg hΞ, mul_comm ε Ξ]
  exact mul_le_mul_of_nonneg_left hFinal hΞ

end BoundedEdgeRegularSubgraphs
