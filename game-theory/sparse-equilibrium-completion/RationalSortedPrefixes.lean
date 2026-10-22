/- AI-assisted formalization under the repository Apache-2.0 license.
The computed rational ordering discharges the sortedness hypothesis of the
paper's quantitative prefix criterion. Efficient prefix scanning is separate. -/
module
public import RationalSortedIndex
public import PrefixViolation
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem cut_violation_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (q v : κ → ℝ) (M r : ℝ) (S : Finset ι) :
    (∑ i ∈ S.map e.toEmbedding, q i * v i) -
        M * mass (S.map e.toEmbedding) q * (r - mass (S.map e.toEmbedding) q) =
      (∑ i ∈ S, q (e i) * v (e i)) -
        M * mass S (fun i => q (e i)) * (r - mass S (fun i => q (e i))) := by
  simp only [mass, Finset.sum_map, Equiv.toEmbedding_apply]

theorem all_cut_violation_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (q v : κ → ℝ) (M r δ : ℝ) :
    (∀ S : Finset κ, (∑ i ∈ S, q i*v i)-M*mass S q*(r-mass S q) ≤ δ) ↔
    ∀ S : Finset ι, (∑ i ∈ S, q (e i)*v (e i))-
      M*mass S (fun i => q (e i))*(r-mass S (fun i => q (e i))) ≤ δ := by
  constructor
  · intro h S
    rw [← cut_violation_reindex]
    exact h _
  · intro h S
    have hs : (S.map e.symm.toEmbedding).map e.toEmbedding = S := by
      ext i
      simp only [Finset.mem_map, Equiv.toEmbedding_apply]
      constructor
      · rintro ⟨j, ⟨k, hk, rfl⟩, rfl⟩
        simpa using hk
      · intro hi
        exact ⟨e.symm i, ⟨i, hi, rfl⟩, e.apply_symm_apply i⟩
    have hh := h (S.map e.symm.toEmbedding)
    rw [← cut_violation_reindex, hs] at hh
    exact hh

theorem rational_sorted_cut_prefix_criterion {m : ℕ}
    (q : Fin m → ℝ) (f : Fin m → ℚ) (M r δ : ℝ)
    (hM : 0 ≤ M) (hq : ∀ i, 0 ≤ q i) :
    (∀ S : Finset (Fin m),
      (∑ i ∈ S, q i*(f i : ℝ))-M*mass S q*(r-mass S q) ≤ δ) ↔
    ∀ l : ℕ, l ≤ (rationalLabelSort f).1.length →
      (∑ i ∈ scorePrefix (rationalLabelSort f).1.length l,
          q (rationalSortedIndex f i)*(f (rationalSortedIndex f i) : ℝ))-
        M*mass (scorePrefix (rationalLabelSort f).1.length l)
          (fun i => q (rationalSortedIndex f i))*
          (r-mass (scorePrefix (rationalLabelSort f).1.length l)
            (fun i => q (rationalSortedIndex f i))) ≤ δ := by
  rw [all_cut_violation_reindex (rationalSortedEquiv f)]
  apply cut_violation_bound_iff_prefix_bound _ _ M r δ hM
  · intro i
    exact hq _
  · intro i j hij
    change (f (rationalSortedIndex f j) : ℝ) ≤ (f (rationalSortedIndex f i) : ℝ)
    exact Rat.cast_le.mpr (rational_sorted_index_antitone f hij)

end
end SparseCompletion
