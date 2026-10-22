/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import CompletionGeometry

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- The weighted cuts and global guards reconstruct every row, including
    rows whose prescribed probability is zero. -/
theorem completion_of_cuts_and_guards {ι : Type*} [Fintype ι]
    (q t : ι → ℝ) (M r ρ : ℝ) (hM : 0 ≤ M)
    (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i = r)
    (hc : Cuts M r q (fun i => t i-ρ)) (hg : ∀ i, t i ≤ ρ+M*r) :
    ∃ B, IsSkew B ∧ (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
      ∀ i, t i+response B q i ≤ ρ := by
  classical
  obtain ⟨B, hB, hw⟩ := cuts_weighted_completion q (fun i => t i-ρ) M r hM hr hc
  let s := Finset.univ.filter fun i => q i ≠ 0
  have hs : ∀ j, j ∉ s → q j = 0 := by
    intro j hj
    by_contra hn
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hn⟩)
  refine ⟨compactCompletion s M B, compactCompletion_skew s M B (fun i _ j _ => hB.1 i j),
    compactCompletion_bounds s M B hM (fun i _ j _ => hB.2 i j), ?_⟩
  intro i
  by_cases hi : i ∈ s
  · have hqi : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm (Finset.mem_filter.mp hi).2)
    have hrow : t i+response B q i ≤ ρ := by
      have hh := hw i
      nlinarith
    have hsum : (∑ j ∈ s, B i j*q j) = response B q i := by
      apply Finset.sum_subset (Finset.subset_univ s)
      intro j _ hj
      rw [hs j hj, mul_zero]
    rw [compactCompletion_response_on s M B q hs i hi, hsum]
    exact hrow
  · rw [compactCompletion_response_off s M r B q hs hr i hi]
    linarith [hg i]

/-- Exact weighted completion criterion, with no positivity requirement on
    individual weights and no division by a probability coordinate. -/
theorem weighted_completion_iff {ι : Type*} [Fintype ι]
    (q t : ι → ℝ) (M r ρ : ℝ) (hM : 0 ≤ M)
    (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i = r) :
    (∃ B, IsSkew B ∧ (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
      ∀ i, t i+response B q i ≤ ρ) ↔
    (∀ i, t i ≤ ρ+M*r) ∧ Cuts M r q (fun i => t i-ρ) := by
  classical
  constructor
  · rintro ⟨B, hsk, hb, hresp⟩
    exact ⟨response_guard q t B M r ρ hq hr (fun i j => (hb i j).1) hresp,
      completion_cuts_necessary q t B M r ρ hq hr hsk (fun i j => (hb i j).1) hresp⟩
  · rintro ⟨hg, hc⟩
    exact completion_of_cuts_and_guards q t M r ρ hM hq hr hc hg

end
end SparseCompletion
