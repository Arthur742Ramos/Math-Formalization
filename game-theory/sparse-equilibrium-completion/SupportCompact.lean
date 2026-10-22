/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ValueStability

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def supportBudget {ν : Type*} [Fintype ν] (s : ℕ) : Set (ν → ℝ) := by
  classical
  exact {x | (Finset.univ.filter fun i => x i ≠ 0).card ≤ s}

theorem support_budget_closed {ν : Type*} [Fintype ν] (s : ℕ) :
    IsClosed (supportBudget (ν := ν) s) := by
  classical
  have he : supportBudget (ν := ν) s=
      ⋃ S : {S : Finset ν // S.card ≤ s}, {x : ν → ℝ | ∀ i, i ∉ S.val → x i=0} := by
    ext x
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
    constructor
    · intro h
      refine ⟨⟨Finset.univ.filter (fun i => x i ≠ 0),h⟩,?_⟩
      intro i hi
      by_contra hx
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hx⟩)
    · rintro ⟨S,hS⟩
      apply le_trans (Finset.card_le_card ?_) S.property
      intro i hi
      by_contra hn
      exact (Finset.mem_filter.mp hi).2 (hS i hn)
  rw [he]
  apply isClosed_iUnion_of_finite
  intro S
  have hz : {x : ν → ℝ | ∀ i, i ∉ S.val → x i=0}=
      ⋂ i, ⋂ (_hi : i ∉ S.val), {x : ν → ℝ | x i=0} := by
    ext x
    simp only [Set.mem_iInter,Set.mem_ofPred_eq]
  rw [hz]
  exact isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_eq (continuous_apply i) continuous_const

theorem support_restricted_compact {ν : Type*} [Fintype ν]
    (X : Set (ν → ℝ)) (hX : IsCompact X) (s : ℕ) : IsCompact (X ∩ supportBudget s) :=
  hX.inter_right (support_budget_closed s)

theorem optimistic_support_value_attained {ν : Type*} [Fintype ν] [Nonempty ν]
    (lo hi : ν → ν → ℝ) (M : ℝ) (X : Set (ν → ℝ)) (s : ℕ)
    (hI : ValidIntervalSystem lo hi M) (hX : IsCompact X)
    (hne : (X ∩ supportBudget s).Nonempty) :
    ∃ A ∈ intervalMatrices lo hi M, ∃ x ∈ X ∩ supportBudget s,
      exploitability A x=optimisticValue lo hi M (X ∩ supportBudget s) :=
  optimistic_value_attained lo hi M _ hI (support_restricted_compact X hX s) hne

theorem optimistic_support_value_stability {ν : Type*} [Fintype ν] [Nonempty ν]
    (lo hi lo' hi' : ν → ν → ℝ) (M δ : ℝ) (X : Set (ν → ℝ)) (s : ℕ)
    (hI : ValidIntervalSystem lo hi M) (hI' : ValidIntervalSystem lo' hi' M)
    (hδ : 0 ≤ δ) (hX : IsCompact X) (hne : (X ∩ supportBudget s).Nonempty)
    (hprob : ∀ x ∈ X, (∀ i, 0 ≤ x i) ∧ (∑ i, x i)=1)
    (hd : ∀ i j, i ≠ j → |lo i j-lo' i j| ≤ δ ∧ |hi i j-hi' i j| ≤ δ) :
    |optimisticValue lo hi M (X ∩ supportBudget s)-optimisticValue lo' hi' M (X ∩ supportBudget s)| ≤ δ :=
  optimistic_value_interval_stability lo hi lo' hi' M δ _ hI hI' hδ
    (support_restricted_compact X hX s) hne (fun x hx => hprob x hx.1) hd

end
end SparseCompletion
