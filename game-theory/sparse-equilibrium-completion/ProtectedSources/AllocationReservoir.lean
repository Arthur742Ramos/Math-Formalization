/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.AllocationValue
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def reservoirRounded {α : Type*} [Fintype α] [DecidableEq α]
    (s p : α → ℝ) (δ : ℝ) (j : α) : α → ℝ :=
  transferredResidual (roundedAllocation s p δ) (removedAnchorMass s p δ) j

theorem reservoir_rounded_mass {α : Type*} [Fintype α] [DecidableEq α]
    (s p : α → ℝ) (δ : ℝ) (j : α) :
    (∑ i, reservoirRounded s p δ j i) = ∑ i, p i := by
  rw [reservoirRounded, transferred_residual_mass]
  unfold removedAnchorMass
  rw [Finset.sum_sub_distrib]
  ring

theorem reservoir_rounded_floors {α : Type*} [Fintype α] [DecidableEq α]
    (s p : α → ℝ) (δ : ℝ) (j : α)
    (hsp : ∀ i, s i ≤ p i) (hδ : 0 < δ) :
    ∀ i, s i ≤ reservoirRounded s p δ j i := by
  intro i
  apply le_trans (rounded_anchor_bounds _ _ _ (hsp i) hδ).1
  apply le_add_of_nonneg_right
  split_ifs
  · exact (removed_anchor_mass_bounds s p δ hsp hδ).1
  · exact le_refl 0

theorem reservoir_rounded_distance {α : Type*} [Fintype α] [DecidableEq α]
    (s p : α → ℝ) (δ : ℝ) (j : α)
    (hsp : ∀ i, s i ≤ p i) (hδ : 0 < δ) :
    (∑ i, |p i-reservoirRounded s p δ j i|) ≤ (2 : ℕ)*(Fintype.card α : ℝ)*δ := by
  have hd := removed_anchor_mass_bounds s p δ hsp hδ
  have ha : (∑ i, |p i-roundedAllocation s p δ i|)=removedAnchorMass s p δ := by
    apply Finset.sum_congr rfl
    intro i _
    exact abs_of_nonneg (sub_nonneg.mpr (rounded_anchor_bounds _ _ _ (hsp i) hδ).2.1)
  calc
    (∑ i, |p i-reservoirRounded s p δ j i|) ≤
        ∑ i, (|p i-roundedAllocation s p δ i|+
          |roundedAllocation s p δ i-reservoirRounded s p δ j i|) := by
      apply Finset.sum_le_sum
      intro i _
      exact abs_sub_le _ _ _
    _ = removedAnchorMass s p δ+removedAnchorMass s p δ := by
      rw [Finset.sum_add_distrib,ha]
      rw [reservoirRounded,transferred_residual_distance _ _ j hd.1]
    _ ≤ _ := by norm_num only [Nat.cast_ofNat]; linarith

def reservoirGridAllocation {α : Type*} [Fintype α] [DecidableEq α]
    (s : α → ℝ) (δ : ℝ) (j : α) (z : α → Fin (1+Nat.floor (1/δ))) : α → ℝ :=
  transferredResidual (fun i => s i+δ*(z i : ℕ))
    (1-∑ i, (s i+δ*(z i : ℕ))) j

theorem reservoir_grid_mass {α : Type*} [Fintype α] [DecidableEq α]
    (s : α → ℝ) (δ : ℝ) (j : α) (z : α → Fin (1+Nat.floor (1/δ))) :
    (∑ i, reservoirGridAllocation s δ j z i)=1 := by
  rw [reservoirGridAllocation,transferred_residual_mass]
  ring

theorem reservoir_rounded_finite_grid {α : Type*} [Fintype α] [DecidableEq α]
    (s p : α → ℝ) (δ : ℝ) (j : α) (hs : ∀ i, 0 ≤ s i)
    (hp : p ∈ floorStrategies s) (hδ : 0 < δ) :
    ∃ z : α → Fin (1+Nat.floor (1/δ)), reservoirRounded s p δ j=reservoirGridAllocation s δ j z := by
  obtain ⟨z,hz⟩ := rounded_allocation_finite_grid s p δ hs
    (fun i => (floor_strategy_coordinate_bounds s p hs hp i).2) hδ
  have he : roundedAllocation s p δ=(fun i => s i+δ*(z i : ℕ)) := funext hz
  have hm : removedAnchorMass s p δ=1-∑ i, (s i+δ*(z i : ℕ)) := by
    unfold removedAnchorMass
    rw [Finset.sum_sub_distrib,hp.2,he]
  exact ⟨z,by rw [reservoirRounded,reservoirGridAllocation,he,hm]⟩

end
end SparseCompletion
