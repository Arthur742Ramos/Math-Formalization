module

public import BoundedEdgeRegularSubgraphs.DensitySurplus
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# Covariances of Gaussian edge sums and the frame inequality
-/

@[expose] public section

open Matrix
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The covariance of two edge sums formed from a vector with covariance
matrix `cov`. -/
def edgePairCovariance (cov : Matrix α α ℝ) (e f : Edge α) : ℝ :=
  (cov e.val.1 f.val.1 + cov e.val.1 f.val.2) +
    (cov e.val.2 f.val.1 + cov e.val.2 f.val.2)

omit [Fintype α] in
/-- Incident pairs use the diagonal bound. Disjoint pairs use only the
off-diagonal bound. -/
theorem abs_edgePairCovariance_le (cov : Matrix α α ℝ) {d o : ℝ} (hod : o ≤ d)
    (hd : ∀ i, |cov i i| ≤ d) (ho : ∀ i j, i ≠ j → |cov i j| ≤ o)
    (e f : Edge α) :
    |edgePairCovariance cov e f| ≤ 4 * d ∧
      (e.val.1 ≠ f.val.1 → e.val.1 ≠ f.val.2 →
        e.val.2 ≠ f.val.1 → e.val.2 ≠ f.val.2 → |edgePairCovariance cov e f| ≤ 4 * o) := by
  have htriangle : |edgePairCovariance cov e f| ≤
      (|cov e.val.1 f.val.1| + |cov e.val.1 f.val.2|) +
        (|cov e.val.2 f.val.1| + |cov e.val.2 f.val.2|) :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
  have hentry (a b : α) : |cov a b| ≤ d := by
    by_cases h : a = b
    · subst b
      exact hd a
    · exact (ho a b h).trans hod
  refine ⟨htriangle.trans ?_, fun h₁ h₂ h₃ h₄ ↦ htriangle.trans ?_⟩
  · linarith only [hentry e.val.1 f.val.1, hentry e.val.1 f.val.2,
      hentry e.val.2 f.val.1, hentry e.val.2 f.val.2]
  · linarith only [ho _ _ h₁, ho _ _ h₂, ho _ _ h₃, ho _ _ h₄]

/-- A uniform absolute row-sum bound for the covariance matrix indexed by
the available edges follows from the vertex covariance row-sum bound. -/
theorem sum_abs_edgePairCovariance_le (cov : Matrix α α ℝ)
    (A : Finset (Edge α)) (e : Edge α) {C : ℝ}
    (hC : ∀ i, (∑ j, |cov i j|) ≤ C) :
    (∑ f ∈ A, |edgePairCovariance cov e f|) ≤ 2 * ((Fintype.card α : ℝ) - 1) * C := by
  let F (f : Edge α) := (|cov e.val.1 f.val.1| + |cov e.val.1 f.val.2|) +
    (|cov e.val.2 f.val.1| + |cov e.val.2 f.val.2|)
  have hn : (0 : ℝ) ≤ (Fintype.card α : ℝ) - 1 := by
    have : Nonempty α := ⟨e.val.1⟩
    have h : 1 ≤ Fintype.card α := Fintype.card_pos
    exact sub_nonneg.mpr (by exact_mod_cast h)
  calc
    _ ≤ ∑ f ∈ A, F f := Finset.sum_le_sum (fun f _ ↦
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _)))
    _ ≤ ∑ f : Edge α, F f :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ by
        dsimp only [F]; positivity)
    _ = ((Fintype.card α : ℝ) - 1) * (∑ j, |cov e.val.1 j|) +
        ((Fintype.card α : ℝ) - 1) * (∑ j, |cov e.val.2 j|) := by
      dsimp only [F]
      rw [Finset.sum_add_distrib, sum_edge_endpoint_values (fun j ↦ |cov e.val.1 j|),
        sum_edge_endpoint_values (fun j ↦ |cov e.val.2 j|)]
    _ ≤ _ := by
      have h₁ := mul_le_mul_of_nonneg_left (hC e.val.1) hn
      have h₂ := mul_le_mul_of_nonneg_left (hC e.val.2) hn
      linarith only [h₁, h₂]

/-- The weighted frame estimate (A.2). The frame normalization says that
the weighted sum of the squared projections is the squared norm. -/
theorem weighted_frame_synthesis_le {ι κ : Type*} [Fintype ι]
    (E : Finset κ) (v : κ → ι → ℝ) (w z : κ → ℝ) {a : ℝ} (ha : 0 < a)
    (hw : ∀ e ∈ E, a ≤ w e)
    (hnorm : ∀ x : ι → ℝ, (∑ e ∈ E, w e * (x ⬝ᵥ v e) ^ 2) = ∑ i, x i ^ 2) :
    (∑ i, (∑ e ∈ E, z e * v e i) ^ 2) ≤ a⁻¹ * ∑ e ∈ E, z e ^ 2 := by
  let x (i : ι) := ∑ e ∈ E, z e * v e i
  let X := ∑ i, x i ^ 2
  have hX : 0 ≤ X := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hD : (∑ e ∈ E, z e * (x ⬝ᵥ v e)) = X := by
    simp only [dotProduct, Finset.mul_sum, X, pow_two]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (∑ e ∈ E, z e * (x i * v e i)) = x i * ∑ e ∈ E, z e * v e i by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ ↦ by ring)]
  have hZ : (∑ e ∈ E, (x ⬝ᵥ v e) ^ 2) ≤ X / a := by
    apply (le_div_iff₀ ha).2
    change (∑ e ∈ E, (x ⬝ᵥ v e) ^ 2) * a ≤ ∑ i, x i ^ 2
    rw [mul_comm, Finset.mul_sum, ← hnorm x]
    exact Finset.sum_le_sum (fun e he ↦ mul_le_mul_of_nonneg_right (hw e he) (sq_nonneg _))
  have hCauchy : X ^ 2 ≤ (∑ e ∈ E, z e ^ 2) * (X / a) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq E z (fun e ↦ x ⬝ᵥ v e)
    rw [hD] at h
    exact h.trans
      (mul_le_mul_of_nonneg_left hZ (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)))
  change X ≤ a⁻¹ * ∑ e ∈ E, z e ^ 2
  rcases hX.eq_or_lt with h | h
  · rw [← h]
    exact mul_nonneg (inv_nonneg.mpr ha.le) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  · apply le_of_mul_le_mul_right _ h
    rw [show (a⁻¹ * ∑ e ∈ E, z e ^ 2) * X = (∑ e ∈ E, z e ^ 2) * (X / a) by
      rw [div_eq_mul_inv]; ring]
    exact (pow_two X).symm.le.trans hCauchy

end BoundedEdgeRegularSubgraphs
