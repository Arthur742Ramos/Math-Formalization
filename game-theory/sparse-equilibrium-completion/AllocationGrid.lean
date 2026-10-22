/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import AllocationRounding

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem rounded_anchor_grid_index (s p δ : ℝ) (hs : 0 ≤ s) (hp : p ≤ 1) (hδ : 0 < δ) :
    Nat.floor ((p-s)/δ) < 1+Nat.floor (1/δ) := by
  have h : (p-s)/δ ≤ 1/δ := div_le_div_of_nonneg_right (by linarith) (le_of_lt hδ)
  have hm := Nat.floor_mono h
  omega

theorem rounded_allocation_finite_grid {α : Type*} (s p : α → ℝ) (δ : ℝ)
    (hs : ∀ i, 0 ≤ s i) (hp : ∀ i, p i ≤ 1) (hδ : 0 < δ) :
    ∃ z : α → Fin (1+Nat.floor (1/δ)),
      ∀ i, roundedAllocation s p δ i=s i+δ*(z i : ℕ) := by
  exact ⟨fun i => ⟨Nat.floor ((p i-s i)/δ),rounded_anchor_grid_index _ _ _ (hs i) (hp i) hδ⟩,
    fun _ => rfl⟩

theorem allocation_grid_card {α : Type*} [Fintype α] [DecidableEq α] (δ : ℝ) :
    Fintype.card (α → Fin (1+Nat.floor (1/δ)))=(1+Nat.floor (1/δ))^Fintype.card α := by
  simp only [Fintype.card_fun,Fintype.card_fin]

theorem allocation_rounding_preserves_floors {α ι : Type*} [Fintype α] [DecidableEq ι]
    (s p : α → ℝ) (t q : ι → ℝ) (δ : ℝ) (j : ι)
    (hsp : ∀ i, s i ≤ p i) (htq : ∀ i, t i ≤ q i) (hδ : 0 < δ) :
    (∀ i, s i ≤ roundedAllocation s p δ i) ∧
      (∀ i, t i ≤ transferredResidual q (removedAnchorMass s p δ) j i) := by
  refine ⟨fun i => (rounded_anchor_bounds _ _ _ (hsp i) hδ).1,?_⟩
  intro i
  apply le_trans (htq i)
  apply le_add_of_nonneg_right
  split_ifs
  · exact (removed_anchor_mass_bounds s p δ hsp hδ).1
  · exact le_refl 0

end
end SparseCompletion
