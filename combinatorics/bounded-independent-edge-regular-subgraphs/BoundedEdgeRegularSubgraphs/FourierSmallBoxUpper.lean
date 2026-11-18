module

public import BoundedEdgeRegularSubgraphs.FourierVolume
public import BoundedEdgeRegularSubgraphs.FourierLocalExpansion
public import BoundedEdgeRegularSubgraphs.GaussianChangeOfVariables
public import BoundedEdgeRegularSubgraphs.GaussianQuarticConcentration
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# The small-box Fourier modulus and the clipped Gaussian exponential
-/

public section

open MeasureTheory Matrix Set
open scoped BigOperators MatrixOrder

namespace BoundedEdgeRegularSubgraphs

/-- The Gaussian normalizer in normalized torus measure. -/
@[expose] noncomputable def phaseGaussianScale {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ((Real.sqrt (2 * Real.pi)) ^ n / Real.sqrt Q.det) / (2 * Real.pi) ^ n

/-- The modulus integral over one small box is bounded by the Gaussian
scale times the expectation of the clipped quartic weight. -/
theorem integral_degreeFourier_smallBox_le_clipped_exp {n : ℕ}
    (A : Finset (Edge (Fin n))) (q : Edge (Fin n) → Icc (0 : ℝ) 1) (d : Fin n → ℤ)
    (hQ : (degreeCovariance A q).PosDef) {r ε : ℝ} (hr : 0 ≤ r) (hr' : 2 * r ≤ 1 / 4)
    (hε : ∀ x ∈ realPhaseBox (α := Fin n) r, ‖degreeFourierLocalError A q x‖ ≤ ε) :
    let Q := degreeCovariance A q
    let B := (CFC.sqrt Q)⁻¹
    let b := fun e ↦ degreeQuarticCoefficient (q e)
    (∫ t in phaseBox (0 : PhaseCircle) r, ‖degreeFourier A q d t‖ ∂phaseLaw) ≤
      Real.exp ε * phaseGaussianScale Q *
        ∫ x, Real.exp (edgeQuartic A b (fun i ↦ clipRadius r ((B *ᵥ x) i))) ∂standardGaussianProduct n := by
  let Q := degreeCovariance A q
  let B := (CFC.sqrt Q)⁻¹
  let b (e : Edge (Fin n)) := degreeQuarticCoefficient (q e)
  let s : ℝ := (2 * Real.pi) ^ n
  let Ξ := (Real.sqrt (2 * Real.pi)) ^ n / Real.sqrt Q.det
  let V (x : Fin n → ℝ) := Real.exp (-(x ⬝ᵥ (Q *ᵥ x)) / 2)
  let H (x : Fin n → ℝ) := edgeQuartic A b (fun i ↦ clipRadius r (x i))
  let W (x : Fin n → ℝ) := Real.exp (H x)
  let M (t : Fin n → PhaseCircle) := ‖degreeFourier A q d t‖
  let P (x : Fin n → ℝ) (i : Fin n) := (x i : PhaseCircle)
  let U := realPhaseBox (α := Fin n) r
  have hU : MeasurableSet U := by
    rw [show U = ⋂ i, {x : Fin n → ℝ | |x i| ≤ r} by ext x; simp [U, realPhaseBox]]
    exact MeasurableSet.iInter (fun i ↦ measurableSet_le
      (continuous_abs.measurable.comp (measurable_pi_apply i)) measurable_const)
  have hs : 0 < s := by dsimp only [s]; positivity
  have hΞ : 0 < Ξ := by
    dsimp only [Ξ]
    exact div_pos (pow_pos (Real.sqrt_pos.mpr (by positivity)) _) (Real.sqrt_pos.mpr hQ.det_pos)
  have hrπ : r < Real.pi := by linarith only [hr', Real.pi_gt_three]
  have hV : Integrable V := by
    apply Integrable.of_integral_ne_zero
    have h := integral_exp_neg_quadratic Q hQ
    rw [Fintype.card_fin] at h
    exact h.trans_ne hΞ.ne'
  have hH : Continuous H := by
    unfold H edgeQuartic clipRadius
    apply continuous_finsetSum
    intro e _
    fun_prop
  have hW : Continuous W := Real.continuous_exp.comp hH
  let K : ℝ := (A.card : ℝ) * ((1 / 96) * (2 * r) ^ 4)
  have hb (e : Edge (Fin n)) (_ : e ∈ A) : |b e| ≤ 1 / 96 := abs_degreeQuarticCoefficient_le _
  have hWbound (x : Fin n → ℝ) : W x ≤ Real.exp K :=
    Real.exp_le_exp.mpr ((le_abs_self (H x)).trans
      (abs_edgeQuartic_clip_le A b (by norm_num) hr hb x))
  have hVI : Integrable (fun x ↦ V x * W x) := by
    apply (hV.const_mul (Real.exp K)).mono'
      (hV.aestronglyMeasurable.mul hW.aestronglyMeasurable)
    exact ae_of_all _ (fun x ↦ by
      change ‖V x * W x‖ ≤ Real.exp K * V x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)),
        mul_comm (Real.exp K) (V x)]
      exact mul_le_mul_of_nonneg_left (hWbound x) (Real.exp_nonneg _))
  have hpoint (x : Fin n → ℝ) (hx : x ∈ U) :
      M (P x) ≤ Real.exp ε * (V x * W x) := by
    have ht (e : Edge (Fin n)) (_ : e ∈ A) : |x e.val.1 + x e.val.2| ≤ 1 / 4 :=
      (abs_add_le _ _).trans (by linarith only [hx e.val.1, hx e.val.2, hr'])
    have hclip : (fun i ↦ clipRadius r (x i)) = x :=
      funext (fun i ↦ clipRadius_eq_of_abs_le (hx i))
    have hRe : (degreeFourierLocalError A q x).re ≤ ε :=
      (Complex.re_le_norm _).trans (hε x hx)
    change ‖degreeFourier A q d (P x)‖ ≤ _
    rw [norm_degreeFourier_eq_exp_local_expansion A q d x ht]
    dsimp only [V, W, H, Q]
    rw [hclip, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [hRe])
  have hI : (∫ x in U, M (P x)) ≤ Real.exp ε * ∫ x, V x * W x := by
    calc
      _ ≤ ∫ x in U, Real.exp ε * (V x * W x) := by
        apply integral_mono_of_nonneg (ae_of_all _ (fun _ ↦ norm_nonneg _)) (hVI.const_mul _).integrableOn
        filter_upwards [ae_restrict_mem hU] with x hx
        exact hpoint x hx
      _ = Real.exp ε * ∫ x in U, V x * W x := by rw [integral_const_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (setIntegral_le_integral hVI
        (ae_of_all _ (fun _ ↦ mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)))) (Real.exp_nonneg _)
  have hchart := integral_phaseBox_zero_eq_real M (continuous_degreeFourier A q d).norm.stronglyMeasurable hrπ
  rw [Fintype.card_fin, smul_eq_mul] at hchart
  change (∫ x in U, M (P x)) = s * ∫ t in phaseBox 0 r, M t ∂phaseLaw at hchart
  rw [hchart] at hI
  have hchange := integral_quadratic_smul_eq_gaussianProduct Q hQ W hW.stronglyMeasurable
  simp only [smul_eq_mul] at hchange
  change (∫ x, V x * W x) = Ξ * ∫ x, W (B *ᵥ x) ∂standardGaussianProduct n at hchange
  rw [hchange] at hI
  change _ ≤ Real.exp ε * (Ξ / s) * ∫ x, W (B *ᵥ x) ∂standardGaussianProduct n
  rw [← mul_div_assoc, div_mul_eq_mul_div]
  apply (le_div_iff₀ hs).2
  simpa only [mul_comm s, mul_assoc] using hI

end BoundedEdgeRegularSubgraphs
