/- AI-assisted formalization under the repository Apache-2.0 license.
Actual finite anchor relabeling, retaining the residual labels literally. -/
module
public import CoverRelabel
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def anchorPullCore {α β : Type*} (e : β ≃ α) (K : α → α → ℝ) : β → β → ℝ :=
  fun h h' => K (e h) (e h')

def anchorPullCross {α β ι : Type*} (e : β ≃ α) (D : ι → α → ℝ) : ι → β → ℝ :=
  fun i h => D i (e h)

theorem block_anchor_pull {α β ι : Type*} (e : β ≃ α)
    (K : α → α → ℝ) (D : ι → α → ℝ) (B : ι → ι → ℝ) :
    blockMatrix (anchorPullCore e K) (anchorPullCross e D) B =
      relabelMatrix (Equiv.sumCongr e (Equiv.refl ι)).symm (blockMatrix K D B) := by
  funext a b
  cases a <;> cases b <;> rfl

theorem weights_anchor_pull {α β ι : Type*} (e : β ≃ α)
    (p : α → ℝ) (q : ι → ℝ) :
    blockWeights (fun h => p (e h)) q =
      relabelWeights (Equiv.sumCongr e (Equiv.refl ι)).symm (blockWeights p q) := by
  funext a
  cases a <;> rfl

theorem response_anchor_pull {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    (e : β ≃ α) (K : α → α → ℝ) (D : ι → α → ℝ) (B : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (a : β ⊕ ι) :
    response (blockMatrix (anchorPullCore e K) (anchorPullCross e D) B)
      (blockWeights (fun h => p (e h)) q) a =
      response (blockMatrix K D B) (blockWeights p q) ((Equiv.sumCongr e (Equiv.refl ι)) a) := by
  rw [block_anchor_pull,weights_anchor_pull,relabel_response]
  rfl

theorem support_anchor_pull {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    (e : β ≃ α) (p : α → ℝ) (q : ι → ℝ) :
    (Finset.univ.filter fun a => blockWeights (fun h => p (e h)) q a ≠ 0).card =
      (Finset.univ.filter fun a => blockWeights p q a ≠ 0).card := by
  classical
  rw [weights_anchor_pull,relabel_support_card]

end
end SparseCompletion
