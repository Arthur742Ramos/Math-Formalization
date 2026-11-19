module

public import BoundedEdgeRegularSubgraphs.GaussianQuarticConcentration
public import BoundedEdgeRegularSubgraphs.GaussianWeightApproximation
public import BoundedEdgeRegularSubgraphs.GaussianLinearMoments
public import BoundedEdgeRegularSubgraphs.FourierStrongConvexity
import Mathlib.Tactic

/-!
# Approximation of the quartic weight on the shrinking box
-/

public section

open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- The finite form of the quartic weight estimate in Lemma A.3. The
restriction to the box appears only in the weight and the scalar tail. -/
theorem integral_abs_quartic_box_weight_sub_le {n : ℕ} (hn : 0 < n)
    (A : Finset (Edge (Fin n))) (b : Edge (Fin n) → ℝ)
    {K r L : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hL : 0 ≤ L)
    (hb : ∀ e ∈ A, |b e| ≤ K) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ v : Fin n → ℝ, (∑ i, (B *ᵥ v) i ^ 2) ≤ L ^ 2 * ∑ i, v i ^ 2) :
    let γ := standardGaussianProduct n
    let h := fun x ↦ edgeQuartic A b (B *ᵥ x)
    let H := fun x ↦ edgeQuartic A b (fun i ↦ clipRadius r ((B *ᵥ x) i))
    let U := {x : Fin n → ℝ | B *ᵥ x ∈ realPhaseBox (α := Fin n) r}
    let m := ∫ x, H x ∂γ
    let ν := ∫ x, h x ∂γ
    let κ := 4 * (2 * r) ^ 3 * K * ((n : ℝ) - 1) * Real.sqrt n * L
    (∫ x, |U.indicator (fun x ↦ Real.exp (h x)) x - Real.exp ν| ∂γ) ≤
      Real.sqrt (Real.exp (2 * m) * (Real.exp (2 * κ ^ 2) - 1)) +
        |Real.exp m - Real.exp ν| + Real.exp ν * γ.real Uᶜ := by
  let γ := standardGaussianProduct n
  let h (x : Fin n → ℝ) := edgeQuartic A b (B *ᵥ x)
  let H (x : Fin n → ℝ) := edgeQuartic A b (fun i ↦ clipRadius r ((B *ᵥ x) i))
  let U := {x : Fin n → ℝ | B *ᵥ x ∈ realPhaseBox (α := Fin n) r}
  let m := ∫ x, H x ∂γ
  let ν := ∫ x, h x ∂γ
  let κ := 4 * (2 * r) ^ 3 * K * ((n : ℝ) - 1) * Real.sqrt n * L
  have hrow (i : Fin n) : Continuous (fun x : Fin n → ℝ ↦ (B *ᵥ x) i) := by
    change Continuous (fun x : Fin n → ℝ ↦ ∑ j, B i j * x j)
    exact continuous_finsetSum _ (fun j _ ↦ continuous_const.mul (continuous_apply j))
  have hU : MeasurableSet U := by
    rw [show U = ⋂ i, {x : Fin n → ℝ | |(B *ᵥ x) i| ≤ r} by ext x; simp [U, realPhaseBox]]
    exact MeasurableSet.iInter (fun i ↦ measurableSet_le (hrow i).abs.measurable measurable_const)
  have hH : Continuous H := by
    unfold H edgeQuartic clipRadius
    apply continuous_finsetSum
    intro e _
    have hc (i : Fin n) : Continuous (fun x : Fin n → ℝ ↦ min r (max (-r) ((B *ᵥ x) i))) :=
      continuous_const.min (continuous_const.max (hrow i))
    exact continuous_const.mul (((hc e.val.1).add (hc e.val.2)).pow 4)
  let b₀ : ℝ := (A.card : ℝ) * (K * (2 * r) ^ 4)
  have hHabs (x : Fin n → ℝ) : |H x| ≤ b₀ := abs_edgeQuartic_clip_le A b hK hr hb (B *ᵥ x)
  have hExp (x : Fin n → ℝ) : Real.exp (H x) ≤ Real.exp b₀ :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans (hHabs x))
  have hW : Integrable (fun x ↦ Real.exp (H x)) γ :=
    Integrable.of_bound (Real.continuous_exp.comp hH).aestronglyMeasurable _ (ae_of_all _ (fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      exact hExp x))
  have hSq : Integrable (fun x ↦ (Real.exp (H x) - Real.exp m) ^ 2) γ := by
    apply Integrable.of_bound (((Real.continuous_exp.comp hH).sub continuous_const).pow 2).aestronglyMeasurable
      ((Real.exp b₀ + Real.exp m) ^ 2)
    exact ae_of_all _ (fun x ↦ by
      change ‖(Real.exp (H x) - Real.exp m) ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_pow]
      apply pow_le_pow_left₀ (abs_nonneg _) _ 2
      have h := abs_add_le (Real.exp (H x)) (-Real.exp m)
      rw [← sub_eq_add_neg, abs_neg, abs_of_nonneg (Real.exp_nonneg (H x)),
        abs_of_nonneg (Real.exp_nonneg m)] at h
      linarith only [h, hExp x])
  have hEq (x : Fin n → ℝ) (hx : x ∈ U) : h x = H x := by
    have hclip : (fun i ↦ clipRadius r ((B *ᵥ x) i)) = B *ᵥ x :=
      funext (fun i ↦ clipRadius_eq_of_abs_le (hx i))
    dsimp only [h, H]
    rw [hclip]
  have hmain := integral_abs_truncated_weight_sub_le U hU (fun x ↦ Real.exp (h x))
    (fun x ↦ Real.exp (H x)) hW (fun x hx ↦ congrArg Real.exp (hEq x hx))
    (Real.exp m) (Real.exp ν) hSq
  rw [abs_of_nonneg (Real.exp_nonneg ν)] at hmain
  let E := EuclideanSpace ℝ (Fin n)
  let T : E → (Fin n → ℝ) := WithLp.ofLp
  have hT : Continuous T := (EuclideanSpace.equiv (Fin n) ℝ).continuous
  have hmeas : Measurable (WithLp.toLp (V := Fin n → ℝ) 2) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.measurable
  have htransport (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) :
      (∫ z, f (T z) ∂stdGaussian E) = ∫ x, f x ∂γ := by
    rw [← map_standardGaussianProduct_toLp]
    exact integral_map hmeas.aemeasurable (hf.comp hT).aestronglyMeasurable
  have hmean : (∫ x, H (T x) ∂stdGaussian E) = m := htransport H hH
  have hh := integral_sq_exp_clippedQuartic_sub_exp_mean_le hn A b hK hr hL hb B hB
  change (∫ x, (Real.exp (H (T x)) - Real.exp (∫ z, H (T z) ∂stdGaussian E)) ^ 2
    ∂stdGaussian E) ≤ Real.exp (2 * (∫ z, H (T z) ∂stdGaussian E)) * (Real.exp (2 * κ ^ 2) - 1) at hh
  rw [hmean, htransport (fun x ↦ (Real.exp (H x) - Real.exp m) ^ 2)
    (((Real.continuous_exp.comp hH).sub continuous_const).pow 2)] at hh
  have hS := Real.sqrt_le_sqrt hh
  exact hmain.trans (by linarith only [hS])

end BoundedEdgeRegularSubgraphs
