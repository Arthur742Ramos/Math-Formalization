/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import SupportCompact

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem endpoint_bounds_from_order {ν : Type*} [LinearOrder ν]
    (lo hi lo' hi' : ν → ν → ℝ) (M δ : ℝ)
    (hI : ValidIntervalSystem lo hi M) (hI' : ValidIntervalSystem lo' hi' M)
    (hd : ∀ i j, i < j → |lo i j-lo' i j| ≤ δ ∧ |hi i j-hi' i j| ≤ δ) :
    ∀ i j, i ≠ j → |lo i j-lo' i j| ≤ δ ∧ |hi i j-hi' i j| ≤ δ := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hd i j h
  · have hh := hd j i h
    have h1 := (hI.2 i j hij).2.2.2
    have h2 := (hI'.2 i j hij).2.2.2
    rw [h1.1,h1.2,h2.1,h2.2]
    constructor
    · simpa only [neg_sub_neg,abs_sub_comm] using hh.2
    · simpa only [neg_sub_neg,abs_sub_comm] using hh.1

theorem optimistic_value_ordered_interval_stability {ν : Type*}
    [Fintype ν] [Nonempty ν] [LinearOrder ν]
    (lo hi lo' hi' : ν → ν → ℝ) (M δ : ℝ) (X : Set (ν → ℝ))
    (hI : ValidIntervalSystem lo hi M) (hI' : ValidIntervalSystem lo' hi' M)
    (hδ : 0 ≤ δ) (hX : IsCompact X) (hne : X.Nonempty)
    (hprob : ∀ x ∈ X, (∀ i, 0 ≤ x i) ∧ (∑ i, x i)=1)
    (hd : ∀ i j, i < j → |lo i j-lo' i j| ≤ δ ∧ |hi i j-hi' i j| ≤ δ) :
    |optimisticValue lo hi M X-optimisticValue lo' hi' M X| ≤ δ :=
  optimistic_value_interval_stability lo hi lo' hi' M δ X hI hI' hδ hX hne hprob
    (endpoint_bounds_from_order lo hi lo' hi' M δ hI hI' hd)

theorem optimistic_support_value_ordered_stability {ν : Type*}
    [Fintype ν] [Nonempty ν] [LinearOrder ν]
    (lo hi lo' hi' : ν → ν → ℝ) (M δ : ℝ) (X : Set (ν → ℝ)) (s : ℕ)
    (hI : ValidIntervalSystem lo hi M) (hI' : ValidIntervalSystem lo' hi' M)
    (hδ : 0 ≤ δ) (hX : IsCompact X) (hne : (X ∩ supportBudget s).Nonempty)
    (hprob : ∀ x ∈ X, (∀ i, 0 ≤ x i) ∧ (∑ i, x i)=1)
    (hd : ∀ i j, i < j → |lo i j-lo' i j| ≤ δ ∧ |hi i j-hi' i j| ≤ δ) :
    |optimisticValue lo hi M (X ∩ supportBudget s)-optimisticValue lo' hi' M (X ∩ supportBudget s)| ≤ δ :=
  optimistic_support_value_stability lo hi lo' hi' M δ X s hI hI' hδ hX hne hprob
    (endpoint_bounds_from_order lo hi lo' hi' M δ hI hI' hd)

end
end SparseCompletion
