/- AI-assisted formalization under the repository Apache-2.0 license.
Literal source allocation mesh; no polynomial-time solver assertion. -/
module
public import ProtectedSources.AllocationApproximation
public import ProtectedSources.AllocationGrid
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem source_allocation_mesh_error {M ε : ℝ} {k : ℕ}
    (hM : 0 < M) (hε : 0 < ε) (hk : 0 < k) :
    0 < ε/((6 : ℕ)*M*(k : ℝ)) ∧
      (2 : ℕ)*M*(k : ℝ)*(ε/((6 : ℕ)*M*(k : ℝ)))=ε/(3 : ℕ) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  constructor
  · positivity
  · field_simp
    ring

theorem optimistic_source_allocation_grid_bounds {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι] [Nonempty (α ⊕ ι)]
    (lo hi : (α ⊕ ι) → (α ⊕ ι) → ℝ) (M ε : ℝ) (s : (α ⊕ ι) → ℝ) (j : ι)
    (hI : ValidIntervalSystem lo hi M) (hs : ∀ i, 0 ≤ s i)
    (hne : (floorStrategies s).Nonempty) (hM : 0 < M) (hε : 0 < ε)
    (hk : 0 < Fintype.card α) :
    optimisticValue lo hi M (floorStrategies s) ≤
      optimisticValue lo hi M (allocationGridStrategies s (ε/((6 : ℕ)*M*(Fintype.card α : ℝ)))) ∧
    optimisticValue lo hi M (allocationGridStrategies s (ε/((6 : ℕ)*M*(Fintype.card α : ℝ)))) ≤
      optimisticValue lo hi M (floorStrategies s)+ε/(3 : ℕ) := by
  obtain ⟨hδ,he⟩ := source_allocation_mesh_error hM hε hk
  have h := optimistic_allocation_grid_bounds lo hi M (ε/((6 : ℕ)*M*(Fintype.card α : ℝ))) s j hI hs hne hδ
  norm_num only [Nat.cast_ofNat] at he
  simpa only [Nat.cast_ofNat,he] using h

end
end SparseCompletion
