module

public import BoundedEdgeRegularSubgraphs.GaussianExpApproximation
public import BoundedEdgeRegularSubgraphs.GaussianQuarticClipping
import Mathlib.Tactic

/-!
# Exponential concentration for the clipped Gaussian quartic
-/

public section

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators NNReal

namespace BoundedEdgeRegularSubgraphs

/-- A coefficient and radius bound controls the clipped quartic everywhere. -/
theorem abs_edgeQuartic_clip_le {n : ℕ} (A : Finset (Edge (Fin n))) (b : Edge (Fin n) → ℝ)
    {K r : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hb : ∀ e ∈ A, |b e| ≤ K) (z : Fin n → ℝ) :
    |edgeQuartic A b (fun i ↦ clipRadius r (z i))| ≤ A.card * (K * (2 * r) ^ 4) := by
  let x (i : Fin n) := clipRadius r (z i)
  change |edgeQuartic A b x| ≤ _
  unfold edgeQuartic
  calc
    _ ≤ ∑ e ∈ A, |b e * (x e.val.1 + x e.val.2) ^ 4| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ A, K * (2 * r) ^ 4 := by
      apply Finset.sum_le_sum
      intro e he
      have h₁ : |x e.val.1| ≤ r := abs_clipRadius_le hr _
      have h₂ : |x e.val.2| ≤ r := abs_clipRadius_le hr _
      have h : |x e.val.1 + x e.val.2| ≤ 2 * r :=
        (abs_add_le _ _).trans (by linarith only [h₁, h₂])
      rw [abs_mul, abs_pow]
      exact mul_le_mul (hb e he) (pow_le_pow_left₀ (abs_nonneg _) h 4) (by positivity) hK
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Apply the Gaussian exponential estimate to the quartic of the clipped
linear image, with its explicit Euclidean Lipschitz constant. -/
theorem integral_sq_exp_clippedQuartic_sub_exp_mean_le {n : ℕ} (hn : 0 < n)
    (A : Finset (Edge (Fin n))) (b : Edge (Fin n) → ℝ)
    {K r L : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hL : 0 ≤ L)
    (hb : ∀ e ∈ A, |b e| ≤ K) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ v : Fin n → ℝ, (∑ i, (B *ᵥ v) i ^ 2) ≤ L ^ 2 * ∑ i, v i ^ 2) :
    let H := fun z : EuclideanSpace ℝ (Fin n) ↦
      edgeQuartic A b (fun i ↦ clipRadius r ((B *ᵥ WithLp.ofLp z) i))
    let κ := 4 * (2 * r) ^ 3 * K * ((n : ℝ) - 1) * Real.sqrt n * L
    let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
    let m := ∫ x, H x ∂γ
    (∫ x, (Real.exp (H x) - Real.exp m) ^ 2 ∂γ) ≤
      Real.exp (2 * m) * (Real.exp (2 * κ ^ 2) - 1) := by
  let H := fun z : EuclideanSpace ℝ (Fin n) ↦
    edgeQuartic A b (fun i ↦ clipRadius r ((B *ᵥ WithLp.ofLp z) i))
  let κ := 4 * (2 * r) ^ 3 * K * ((n : ℝ) - 1) * Real.sqrt n * L
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hκ : 0 ≤ κ := by
    dsimp only [κ]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hn₁))
      (Real.sqrt_nonneg _)) hL
  have hLip : LipschitzWith (⟨κ, hκ⟩ : ℝ≥0) H := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, EuclideanSpace.dist_eq]
    simp only [Real.dist_eq, sq_abs]
    change _ ≤ κ * _
    have h := abs_edgeQuartic_clip_linear_sub_le A b hK hr hL hb B hB (WithLp.ofLp x) (WithLp.ofLp y)
    simpa only [H, κ, Fintype.card_fin, mul_assoc] using h
  exact integral_sq_exp_sub_exp_mean_le hn H ⟨κ, hκ⟩ hLip (fun x ↦
    abs_edgeQuartic_clip_le A b hK hr hb (B *ᵥ WithLp.ofLp x))

end BoundedEdgeRegularSubgraphs
