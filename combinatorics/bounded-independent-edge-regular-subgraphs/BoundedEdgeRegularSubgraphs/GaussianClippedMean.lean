module

public import BoundedEdgeRegularSubgraphs.GaussianQuarticConcentration
public import BoundedEdgeRegularSubgraphs.GaussianCubicMoment
import Mathlib.Tactic

/-!
# A uniform bound on the mean of the clipped quartic
-/

public section

open MeasureTheory Matrix
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

private theorem abs_clipRadius_le_abs {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    |clipRadius r x| ≤ |x| := by
  by_cases hx : |x| ≤ r
  · rw [clipRadius_eq_of_abs_le hx]
  · exact (abs_clipRadius_le hr x).trans (lt_of_not_ge hx).le

private theorem add_pow_four_le (x y : ℝ) :
    (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  have h₁ : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith only [sq_nonneg (x - y)]
  have h₂ : (x ^ 2 + y ^ 2) ^ 2 ≤ 2 * (x ^ 4 + y ^ 4) := by
    nlinarith only [sq_nonneg (x ^ 2 - y ^ 2)]
  calc
    _ = ((x + y) ^ 2) ^ 2 := by ring
    _ ≤ (2 * (x ^ 2 + y ^ 2)) ^ 2 := pow_le_pow_left₀ (by positivity) h₁ 2
    _ ≤ _ := by nlinarith only [h₂]

/-- Clipping does not increase any coordinate magnitude. The resulting
bound involves the fourth moments of the unclipped coordinates. -/
theorem abs_clipped_edgeQuartic_le_coordinate_fourth {n : ℕ} (hn : 0 < n)
    (A : Finset (Edge (Fin n))) (b : Edge (Fin n) → ℝ) {K r : ℝ}
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hb : ∀ e ∈ A, |b e| ≤ K) (x : Fin n → ℝ) :
    |edgeQuartic A b (fun i ↦ clipRadius r (x i))| ≤
      8 * K * ((n : ℝ) - 1) * ∑ i, x i ^ 4 := by
  let u (i : Fin n) := clipRadius r (x i)
  have hpoint (e : Edge (Fin n)) (he : e ∈ A) :
      |b e * (u e.val.1 + u e.val.2) ^ 4| ≤
        8 * K * (x e.val.1 ^ 4 + x e.val.2 ^ 4) := by
    have h := (abs_add_le _ _).trans (add_le_add (abs_clipRadius_le_abs hr (x e.val.1))
      (abs_clipRadius_le_abs hr (x e.val.2)))
    have hh := (pow_le_pow_left₀ (abs_nonneg _) h 4).trans
      (add_pow_four_le |x e.val.1| |x e.val.2|)
    rw [abs_mul, abs_pow]
    have hp := mul_le_mul (hb e he) hh (by positivity) hK
    have hfour (a : ℝ) : |a| ^ 4 = a ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, sq_abs, ← pow_mul]
    simp_rw [hfour] at hp ⊢
    dsimp only [u]
    nlinarith only [hp]
  change |edgeQuartic A b u| ≤ _
  unfold edgeQuartic
  calc
    _ ≤ ∑ e ∈ A, |b e * (u e.val.1 + u e.val.2) ^ 4| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ A, 8 * K * (x e.val.1 ^ 4 + x e.val.2 ^ 4) := Finset.sum_le_sum hpoint
    _ ≤ ∑ e : Edge (Fin n), 8 * K * (x e.val.1 ^ 4 + x e.val.2 ^ 4) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ by positivity)
    _ = _ := by
      rw [← Finset.mul_sum, sum_edge_endpoint_values (fun i : Fin n ↦ x i ^ 4),
        Fintype.card_fin, mul_assoc]
      ring

/-- For coordinate variances at most (D), the mean absolute clipped
quartic is bounded uniformly by (24K(n-1)nD^2). -/
theorem integral_abs_clipped_edgeQuartic_le {n : ℕ} (hn : 0 < n)
    (A : Finset (Edge (Fin n))) (b : Edge (Fin n) → ℝ) {K r D : ℝ}
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hb : ∀ e ∈ A, |b e| ≤ K) (B : Matrix (Fin n) (Fin n) ℝ)
    (hD : ∀ i, (∑ j, B i j ^ 2) ≤ D) :
    (∫ x, |edgeQuartic A b (fun i ↦ clipRadius r ((B *ᵥ x) i))| ∂standardGaussianProduct n) ≤
      24 * K * ((n : ℝ) - 1) * n * D ^ 2 := by
  let γ := standardGaussianProduct n
  let H (x : Fin n → ℝ) := edgeQuartic A b (fun i ↦ clipRadius r ((B *ᵥ x) i))
  have hrow (i : Fin n) : Continuous (fun x ↦ (B *ᵥ x) i) := by
    change Continuous (fun x : Fin n → ℝ ↦ ∑ j, B i j * x j)
    exact continuous_finsetSum _ (fun j _ ↦ continuous_const.mul (continuous_apply j))
  have hH : Continuous H := by
    unfold H edgeQuartic
    apply continuous_finsetSum
    intro e _
    unfold clipRadius
    have h (i : Fin n) : Continuous (fun x : Fin n → ℝ ↦ min r (max (-r) ((B *ᵥ x) i))) :=
      continuous_const.min (continuous_const.max (hrow i))
    exact continuous_const.mul (((h e.val.1).add (h e.val.2)).pow 4)
  have hi : Integrable (fun x ↦ |H x|) γ := by
    apply Integrable.of_bound hH.abs.aestronglyMeasurable (A.card * (K * (2 * r) ^ 4))
    exact ae_of_all _ (fun x ↦ by
      rw [Real.norm_eq_abs, abs_abs]
      exact abs_edgeQuartic_clip_le A b hK hr hb (B *ᵥ x))
  have hj (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n))) :
      Integrable (fun x ↦ (B *ᵥ x) i ^ 4) γ := by
    have hh (x : Fin n → ℝ) : MvPolynomial.eval x (linearPolynomial (B i) ^ 4) = (B *ᵥ x) i ^ 4 := by
      rw [map_pow, eval_linearPolynomial]
      rfl
    rw [← funext hh]
    exact integrable_eval_standardGaussianProduct _
  have hnon : 0 ≤ 8 * K * ((n : ℝ) - 1) := by
    have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_nonneg (by positivity) (sub_nonneg.mpr h)
  have h := integral_mono hi ((integrable_finsetSum _ hj).const_mul (8 * K * ((n : ℝ) - 1)))
    (fun x ↦ abs_clipped_edgeQuartic_le_coordinate_fourth hn A b hK hr hb (B *ᵥ x))
  rw [integral_const_mul, integral_finsetSum _ hj] at h
  refine h.trans ?_
  have hM (i : Fin n) : (∫ x, (B *ᵥ x) i ^ 4 ∂γ) ≤ 3 * D ^ 2 := by
    have hs := integral_even_pow_dotProduct_standardGaussianProduct (B i) 2
    norm_num [Finset.prod_range_succ] at hs
    have hd := pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ ↦ sq_nonneg (B i j))) (hD i) 2
    change (∫ x, (B i ⬝ᵥ x) ^ 4 ∂γ) ≤ _
    linarith only [hs, hd]
  calc
    _ ≤ 8 * K * ((n : ℝ) - 1) * ∑ _ : Fin n, 3 * D ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ hM i)) hnon
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end BoundedEdgeRegularSubgraphs
