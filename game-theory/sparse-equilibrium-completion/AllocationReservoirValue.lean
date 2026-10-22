/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import AllocationReservoir
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem reservoir_rounding_in_floor_strategies {α : Type*} [Fintype α] [DecidableEq α]
    (s p : α → ℝ) (δ : ℝ) (j : α) (hp : p ∈ floorStrategies s) (hδ : 0 < δ) :
    reservoirRounded s p δ j ∈ floorStrategies s :=
  ⟨reservoir_rounded_floors s p δ j hp.1 hδ,(reservoir_rounded_mass s p δ j).trans hp.2⟩

theorem reservoir_rounding_value_bound {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (s p : α → ℝ) (δ M : ℝ) (j : α) (A : α → α → ℝ)
    (hsp : ∀ i, s i ≤ p i) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hA : ∀ i l, |A i l| ≤ M) :
    exploitability A (reservoirRounded s p δ j) ≤
      exploitability A p+(2 : ℕ)*M*(Fintype.card α : ℝ)*δ := by
  have h := (abs_le.mp (exploitability_strategy_distance A p
    (reservoirRounded s p δ j) M hA)).1
  have hd := mul_le_mul_of_nonneg_left (reservoir_rounded_distance s p δ j hsp hδ) hM
  norm_num only [Nat.cast_ofNat] at hd ⊢
  nlinarith

theorem reservoir_grid_approximation {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (s p : α → ℝ) (δ M : ℝ) (j : α) (A : α → α → ℝ)
    (hs : ∀ i, 0 ≤ s i) (hp : p ∈ floorStrategies s) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hA : ∀ i l, |A i l| ≤ M) :
    ∃ z : α → Fin (1+Nat.floor (1/δ)),
      reservoirGridAllocation s δ j z ∈ floorStrategies s ∧
      exploitability A (reservoirGridAllocation s δ j z) ≤
        exploitability A p+(2 : ℕ)*M*(Fintype.card α : ℝ)*δ := by
  obtain ⟨z,hz⟩ := reservoir_rounded_finite_grid s p δ j hs hp hδ
  exact ⟨z,hz ▸ reservoir_rounding_in_floor_strategies s p δ j hp hδ,
    hz ▸ reservoir_rounding_value_bound s p δ M j A hp.1 hδ hM hA⟩

end
end SparseCompletion
