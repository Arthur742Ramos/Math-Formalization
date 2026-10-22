/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import IntervalProjection

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem projected_block_intervals {ι α : Type*} (K : α → α → ℝ) (D : ι → α → ℝ)
    (B B' : ι → ι → ℝ) (lo hi : (α ⊕ ι) → (α ⊕ ι) → ℝ)
    (hI : offDiagonalIntervals lo hi (blockMatrix K D B))
    (hlu : ∀ i j, i ≠ j → lo (.inr i) (.inr j) ≤ hi (.inr i) (.inr j)) :
    offDiagonalIntervals lo hi (blockMatrix K D
      (projectedResidual (fun i j => lo (.inr i) (.inr j)) (fun i j => hi (.inr i) (.inr j)) B')) := by
  intro a b hab
  cases a with
  | inl h =>
    cases b with
    | inl h' => exact hI (.inl h) (.inl h') hab
    | inr j => exact hI (.inl h) (.inr j) hab
  | inr i =>
    cases b with
    | inl h => exact hI (.inr i) (.inl h) hab
    | inr j =>
      have hij : i ≠ j := fun he => hab (congrArg Sum.inr he)
      exact projected_residual_interval _ _ B' hlu i j hij

theorem residual_projection_response_bound {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (D : ι → α → ℝ) (B lo hi : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (M β r τ : ℝ)
    (hβ : 0 ≤ β) (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=r)
    (hB : IsSkew B) (hb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hlu : ∀ i j, i ≠ j → lo i j ≤ hi i j)
    (hlo : ∀ i j, i ≠ j → -M ≤ lo i j)
    (hloss : ∀ i j, i ≠ j → intervalLoss M (lo i j) (hi i j) ≤ β)
    (hrows : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ τ) :
    ∀ a, response (blockMatrix K D (projectedResidual lo hi B)) (blockWeights p q) a ≤ τ+β*r := by
  have hr : 0 ≤ r := by rw [←hm]; exact Finset.sum_nonneg fun i _ => hq i
  intro a
  cases a with
  | inl h =>
    rw [block_response_anchor]
    have ha := hrows (.inl h)
    rw [block_response_anchor] at ha
    exact le_trans ha (by nlinarith)
  | inr i =>
    rw [block_response_residual]
    have ha := hrows (.inr i)
    rw [block_response_residual] at ha
    have hp := response_perturbation (projectedResidual lo hi B) B q β r hq hm
      (projected_residual_distance lo hi B M β hβ hB hb hlu hlo hloss) i
    have hh := (abs_le.mp hp).2
    linarith

end
end SparseCompletion
