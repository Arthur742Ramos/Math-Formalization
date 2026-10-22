/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import AllocationGrid
public import AllocationResponse

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def floorStrategies {ν : Type*} [Fintype ν] (s : ν → ℝ) : Set (ν → ℝ) :=
  {x | (∀ i, s i ≤ x i) ∧ (∑ i, x i)=1}

theorem floor_strategy_coordinate_bounds {ν : Type*} [Fintype ν]
    (s x : ν → ℝ) (hs : ∀ i, 0 ≤ s i) (hx : x ∈ floorStrategies s) (i : ν) :
    0 ≤ x i ∧ x i ≤ 1 := by
  have hn : ∀ j, 0 ≤ x j := fun j => le_trans (hs j) (hx.1 j)
  refine ⟨hn i,?_⟩
  rw [←hx.2]
  exact Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)

theorem floor_strategies_compact {ν : Type*} [Fintype ν]
    (s : ν → ℝ) (hs : ∀ i, 0 ≤ s i) : IsCompact (floorStrategies s) := by
  have hc : IsClosed (floorStrategies s) := by
    have he : floorStrategies s=
        (⋂ i, {x : ν → ℝ | s i ≤ x i}) ∩ {x | (∑ i, x i)=1} := by
      ext x
      simp only [floorStrategies,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]
    rw [he]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  exact isCompact_Icc.of_isClosed_subset hc (fun x hx =>
    ⟨fun i => (floor_strategy_coordinate_bounds s x hs hx i).1,
      fun i => (floor_strategy_coordinate_bounds s x hs hx i).2⟩)

def allocationGridStrategies {α ι : Type*} [Fintype α] [Fintype ι]
    (s : (α ⊕ ι) → ℝ) (δ : ℝ) : Set ((α ⊕ ι) → ℝ) :=
  floorStrategies s ∩ {x | ∃ z : α → Fin (1+Nat.floor (1/δ)),
    ∀ i, x (Sum.inl i)=s (Sum.inl i)+δ*(z i : ℕ)}

theorem allocation_grid_strategies_compact {α ι : Type*} [Fintype α] [Fintype ι]
    (s : (α ⊕ ι) → ℝ) (δ : ℝ) (hs : ∀ i, 0 ≤ s i) :
    IsCompact (allocationGridStrategies s δ) := by
  classical
  apply (floor_strategies_compact s hs).inter_right
  have he : {x : (α ⊕ ι) → ℝ | ∃ z : α → Fin (1+Nat.floor (1/δ)),
      ∀ i, x (Sum.inl i)=s (Sum.inl i)+δ*(z i : ℕ)}=
      ⋃ z : α → Fin (1+Nat.floor (1/δ)),
        ⋂ i, {x | x (Sum.inl i)=s (Sum.inl i)+δ*(z i : ℕ)} := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_iInter]
  rw [he]
  exact isClosed_iUnion_of_finite fun z => isClosed_iInter fun i =>
    isClosed_eq (continuous_apply _) continuous_const

theorem allocation_rounding_in_grid {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (s : (α ⊕ ι) → ℝ) (x : (α ⊕ ι) → ℝ) (δ : ℝ) (j : ι)
    (hs : ∀ i, 0 ≤ s i) (hx : x ∈ floorStrategies s) (hδ : 0 < δ) :
    blockWeights (roundedAllocation (fun i => s (Sum.inl i)) (fun i => x (Sum.inl i)) δ)
      (transferredResidual (fun i => x (Sum.inr i))
        (removedAnchorMass (fun i => s (Sum.inl i)) (fun i => x (Sum.inl i)) δ) j) ∈
      allocationGridStrategies s δ := by
  have hsp := fun i => hx.1 (Sum.inl i)
  have htq := fun i => hx.1 (Sum.inr i)
  have hf := allocation_rounding_preserves_floors _ _ _ _ δ j hsp htq hδ
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro i
    cases i with
    | inl i => exact hf.1 i
    | inr i => exact hf.2 i
  · rw [blockWeights_mass,allocation_rounding_mass]
    exact (Fintype.sum_sum_type x).symm.trans hx.2
  · obtain ⟨z,hz⟩ := rounded_allocation_finite_grid
      (fun i => s (Sum.inl i)) (fun i => x (Sum.inl i)) δ
      (fun i => hs (Sum.inl i))
      (fun i => (floor_strategy_coordinate_bounds s x hs hx (Sum.inl i)).2) hδ
    exact ⟨z,hz⟩

end
end SparseCompletion
