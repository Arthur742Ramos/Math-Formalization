/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.AllocationValue

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem floor_strategies_nonempty {ν : Type*} [Fintype ν] [DecidableEq ν]
    (s : ν → ℝ) (j : ν) (hm : (∑ i, s i) ≤ 1) : (floorStrategies s).Nonempty := by
  refine ⟨transferredResidual s (1-∑ i, s i) j,?_,?_⟩
  · intro i
    apply le_add_of_nonneg_right
    split_ifs
    · linarith
    · exact le_refl 0
  · rw [transferred_residual_mass]
    ring

theorem allocation_grid_nonempty {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (s : (α ⊕ ι) → ℝ) (δ : ℝ) (j : ι)
    (hs : ∀ i, 0 ≤ s i) (hne : (floorStrategies s).Nonempty) (hδ : 0 < δ) :
    (allocationGridStrategies s δ).Nonempty := by
  obtain ⟨x,hx⟩ := hne
  exact ⟨_,allocation_rounding_in_grid s x δ j hs hx hδ⟩

theorem optimistic_allocation_grid_bounds {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι] [Nonempty (α ⊕ ι)]
    (lo hi : (α ⊕ ι) → (α ⊕ ι) → ℝ) (M δ : ℝ) (s : (α ⊕ ι) → ℝ) (j : ι)
    (hI : ValidIntervalSystem lo hi M) (hs : ∀ i, 0 ≤ s i)
    (hne : (floorStrategies s).Nonempty) (hδ : 0 < δ) :
    optimisticValue lo hi M (floorStrategies s) ≤
        optimisticValue lo hi M (allocationGridStrategies s δ) ∧
    optimisticValue lo hi M (allocationGridStrategies s δ) ≤
        optimisticValue lo hi M (floorStrategies s)+(2 : ℕ)*M*(Fintype.card α : ℝ)*δ := by
  have hc := floor_strategies_compact s hs
  have hg := allocation_grid_strategies_compact s δ hs
  have hgn := allocation_grid_nonempty s δ j hs hne hδ
  constructor
  · obtain ⟨A,hA,x,hx,he⟩ := optimistic_value_attained lo hi M _ hI hg hgn
    have hh := optimistic_value_le_witness lo hi M _ hc A x hA hx.1
    rwa [he] at hh
  · obtain ⟨A,hA,x,hx,he⟩ := optimistic_value_attained lo hi M _ hI hc hne
    let p := fun i => x (Sum.inl i)
    let q := fun i => x (Sum.inr i)
    let t := fun i => s (Sum.inl i)
    have hxdec : blockWeights p q=x := by ext i; cases i <;> rfl
    let x' := blockWeights (roundedAllocation t p δ)
      (transferredResidual q (removedAnchorMass t p δ) j)
    have hx' : x' ∈ allocationGridStrategies s δ := allocation_rounding_in_grid s x δ j hs hx hδ
    have hv := optimistic_value_le_witness lo hi M _ hg A x' hA hx'
    have hb : ∀ i j, |A i j| ≤ M := fun i j => abs_le.mpr (hA.1.2 i j)
    have hh := allocation_rounding_value_bound t p q δ M j A
      (fun i => hx.1 (Sum.inl i)) hδ hI.1 hb
    rw [hxdec,he] at hh
    exact le_trans hv hh

end
end SparseCompletion
