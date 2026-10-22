/- AI-assisted formalization under the repository Apache-2.0 license.
Executable descending rational-score sorting with original labels retained.
The counter measures calls to the score comparator, not bit operations. -/
module
public import CountedMergeSort
public import Mathlib.Algebra.Order.Ring.Rat
@[expose] public section
namespace SparseCompletion

def rationalScoreLe {α : Type*} (a b : α × ℚ) : Bool := decide (b.2 ≤ a.2)

theorem rational_score_le_trans {α : Type*} (a b c : α × ℚ)
    (hab : rationalScoreLe a b) (hbc : rationalScoreLe b c) : rationalScoreLe a c := by
  simp only [rationalScoreLe, decide_eq_true_eq] at *
  exact le_trans hbc hab

theorem rational_score_le_total {α : Type*} (a b : α × ℚ) :
    rationalScoreLe a b = true ∨ rationalScoreLe b a = true := by
  simp only [rationalScoreLe, decide_eq_true_eq]
  exact le_total _ _

def rationalScoreSort {α : Type*} (xs : List (α × ℚ)) : List (α × ℚ) × ℕ :=
  countedMergeSort rationalScoreLe xs

theorem rational_score_sort_perm {α : Type*} (xs : List (α × ℚ)) :
    (rationalScoreSort xs).1.Perm xs := counted_merge_sort_perm _ _

theorem rational_score_sort_descending {α : Type*} (xs : List (α × ℚ)) :
    (rationalScoreSort xs).1.Pairwise (fun a b => b.2 ≤ a.2) := by
  have h := counted_merge_sort_pairwise rationalScoreLe rational_score_le_trans
    rational_score_le_total xs
  simpa only [rationalScoreSort, rationalScoreLe, decide_eq_true_eq] using h

theorem rational_score_sort_length {α : Type*} (xs : List (α × ℚ)) :
    (rationalScoreSort xs).1.length = xs.length := counted_merge_sort_length _ _

theorem rational_score_sort_comparisons {α : Type*} (xs : List (α × ℚ)) :
    (rationalScoreSort xs).2 ≤ xs.length * (Nat.log2 xs.length + 1) :=
  counted_merge_sort_log_bound _ _

theorem rational_score_sort_stored_score {α : Type*} (f : α → ℚ)
    (xs : List (α × ℚ)) (h : ∀ a ∈ xs, a.2 = f a.1) :
    ∀ a ∈ (rationalScoreSort xs).1, a.2 = f a.1 := by
  intro a ha
  exact h a ((rational_score_sort_perm xs).mem_iff.mp ha)

end SparseCompletion
