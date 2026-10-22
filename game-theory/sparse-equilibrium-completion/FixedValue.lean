/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import GapFeasibility
public import OptimisticValue

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def fixedGameValue {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty (α ⊕ ι)]
    (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ) (M : ℝ) (R : Set (ι → ℝ)) : ℝ :=
  sInf ((fun z : (ι → ι → ℝ) × (ι → ℝ) =>
    exploitability (blockMatrix K D z.1) (blockWeights p z.2)) '' (skewBox M ×ˢ R))

theorem fixed_game_exploitability_continuous {ι α : Type*} [Fintype ι] [Fintype α]
    [Nonempty (α ⊕ ι)] (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ) :
    Continuous (fun z : (ι → ι → ℝ) × (ι → ℝ) =>
      exploitability (blockMatrix K D z.1) (blockWeights p z.2)) := by
  unfold exploitability
  apply Continuous.finset_sup'_apply
  intro a _
  cases a with
  | inl h =>
    simp only [block_response_anchor,anchorResponse]
    fun_prop
  | inr i =>
    simp only [response,Fintype.sum_sum_type,blockMatrix,blockWeights,Sum.elim_inl,Sum.elim_inr]
    fun_prop

theorem fixed_game_value_attained {ι α : Type*} [Fintype ι] [Fintype α]
    [Nonempty (α ⊕ ι)] (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ)
    (M : ℝ) (R : Set (ι → ℝ)) (hM : 0 ≤ M) (hR : IsCompact R) (hne : R.Nonempty) :
    ∃ B ∈ skewBox M, ∃ q ∈ R,
      exploitability (blockMatrix K D B) (blockWeights p q)=fixedGameValue K D p M R := by
  have hc := ((skewBox_compact M).prod hR).image (fixed_game_exploitability_continuous K D p)
  have hn := ((show (skewBox (ι := ι) M).Nonempty from ⟨0,skewBox_zero M hM⟩).prod hne).image
    (fun z : (ι → ι → ℝ) × (ι → ℝ) => exploitability (blockMatrix K D z.1) (blockWeights p z.2))
  obtain ⟨⟨B,q⟩,⟨hB,hq⟩,he⟩ := hc.sInf_mem hn
  exact ⟨B,hB,q,hq,he⟩

theorem fixed_game_value_le_witness {ι α : Type*} [Fintype ι] [Fintype α]
    [Nonempty (α ⊕ ι)] (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ)
    (M : ℝ) (R : Set (ι → ℝ)) (hR : IsCompact R)
    (B : ι → ι → ℝ) (q : ι → ℝ) (hB : B ∈ skewBox M) (hq : q ∈ R) :
    fixedGameValue K D p M R ≤ exploitability (blockMatrix K D B) (blockWeights p q) := by
  apply csInf_le (((skewBox_compact M).prod hR).image (fixed_game_exploitability_continuous K D p)).bddBelow
  exact ⟨(B,q),⟨hB,hq⟩,rfl⟩

end
end SparseCompletion
