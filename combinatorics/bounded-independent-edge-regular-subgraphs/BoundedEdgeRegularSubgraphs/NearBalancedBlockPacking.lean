module

public import BoundedEdgeRegularSubgraphs.DisjointBlockPacking
public import BoundedEdgeRegularSubgraphs.RowSampleApproximation
import Mathlib.Tactic

/-!
# Uniformly near-balanced disjoint samples from large cells
-/

public section

open Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- Extract a fixed-size block from each available near-balanced cell.
The result is the deterministic packing step in Theorem 6.1. -/
theorem exists_disjoint_nearBalanced_block_packing {α : Type*} [DecidableEq α]
    (s : Finset α) (q : α → α → ℝ) {m : ℕ} (hm : 2 ≤ m)
    {ξ a v : ℝ} (hv : 0 ≤ v)
    (hq : ∀ i ∈ s, ∀ j ∈ s.erase i, q i j ∈ Icc (0 : ℝ) 1)
    (hsmall : 2 * (m : ℝ) * Real.exp (-2 * ((m - 1 : ℕ) : ℝ) * v ^ 2) < 1)
    (hcell : ∀ R ⊆ s, s.card ≤ 2 * R.card → ∃ U ⊆ R, m ≤ U.card ∧
      ∃ p ∈ Icc ξ (1 - ξ), ∀ i ∈ U, |sampleRowMean U q i - p| ≤ a) :
    ∃ B : Finset (Finset α),
      (∀ T ∈ B, T ⊆ s ∧ T.card = m ∧
        ∃ p ∈ Icc ξ (1 - ξ), ∀ i ∈ T, |sampleRowMean T q i - p| ≤ a + v) ∧
      (B : Set (Finset α)).PairwiseDisjoint id ∧ s.card < 2 * (B.card * m) := by
  apply exists_disjoint_block_packing s (show 0 < m by omega)
  intro R hRs hRc
  obtain ⟨U, hUR, hUm, p, hp, hUp⟩ := hcell R hRs hRc
  have hQs (i : α) (hi : i ∈ U) (j : α) (hj : j ∈ U.erase i) :
      q i j ∈ Icc (0 : ℝ) 1 :=
    hq i (hRs (hUR hi)) j (Finset.erase_subset_erase i (hUR.trans hRs) hj)
  obtain ⟨T, hTU, hTm, hTr⟩ := exists_sample_rowMean_close U q hm hUm hQs hv hsmall
  refine ⟨T, hTU.trans hUR, hTm, p, hp, fun i hi ↦ ?_⟩
  have h := abs_add_le (sampleRowMean T q i - sampleRowMean U q i) (sampleRowMean U q i - p)
  rw [sub_add_sub_cancel] at h
  exact h.trans (by linarith only [hTr i hi, hUp i (hTU hi)])

end BoundedEdgeRegularSubgraphs
