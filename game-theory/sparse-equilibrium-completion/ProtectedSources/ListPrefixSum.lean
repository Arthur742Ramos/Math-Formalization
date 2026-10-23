/- AI-assisted formalization under the repository Apache-2.0 license.
Bridge from executable list prefixes to the finite-index prefix convention. -/
module
public import ProtectedSources.RationalSortedPrefixes
public import ProtectedSources.RationalPrefixScan
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem list_take_sum_indexed {α β : Type*} [AddCommMonoid β]
    (xs : List α) (f : α → β) (l : ℕ) :
    ((xs.take l).map f).sum =
      ∑ i : Fin xs.length, if i.val < l then f (xs.get i) else 0 := by
  induction xs generalizing l with
  | nil => simp
  | cons a xs ih =>
    cases l with
    | zero => simp
    | succ l =>
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.length_cons]
      rw [Fin.sum_univ_succ, ih]
      simp

theorem list_take_sum_scorePrefix {α β : Type*} [AddCommMonoid β]
    (xs : List α) (f : α → β) (l : ℕ) :
    ((xs.take l).map f).sum =
      ∑ i ∈ scorePrefix xs.length l, f (xs.get i) := by
  rw [list_take_sum_indexed]
  simp only [scorePrefix, Finset.sum_filter]

end SparseCompletion
