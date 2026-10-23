/- AI-assisted formalization under the repository Apache-2.0 license.
Construct the returned original-label Finset directly from its proved Nodup
prefix. Its data path uses take/map and the Finset constructor, without dedup.
No allocation, machine or bit-cost theorem is asserted. -/
module
public import ProtectedSources.RationalViolationPayload
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalNodupPrefixLabels {m : ℕ} (xs : List (Fin m × ℚ))
    (hn : (xs.map Prod.fst).Nodup) (l : ℕ) : Finset (Fin m) :=
  ⟨((xs.take l).map Prod.fst : Multiset (Fin m)), by
    rw [Multiset.coe_nodup,List.map_take]
    exact hn.take⟩

theorem rational_nodup_prefix_labels_data {m : ℕ} (xs : List (Fin m × ℚ))
    (hn : (xs.map Prod.fst).Nodup) (l : ℕ) :
    (rationalNodupPrefixLabels xs hn l).val =
      ((xs.take l).map Prod.fst : Multiset (Fin m)) := rfl

theorem rational_nodup_prefix_labels_eq {m : ℕ} (xs : List (Fin m × ℚ))
    (hn : (xs.map Prod.fst).Nodup) (l : ℕ) :
    rationalNodupPrefixLabels xs hn l = ((xs.take l).map Prod.fst).toFinset := by
  apply List.toFinset_eq

def rationalNodupSortedViolation {m : ℕ} (M r δ : ℚ) (q f : Fin m → ℚ) :
    Option (Finset (Fin m)) × ℕ :=
  let sorted := rationalLabelSort f
  let scan := rationalViolationSearch M r δ 0 0
    (sorted.1.map (fun a => (q a.1,q a.1*a.2)))
  (scan.1.map (fun l => rationalNodupPrefixLabels sorted.1
    (rational_label_sort_nodup f) l), sorted.2+scan.2)

theorem rational_nodup_sorted_violation_eq {m : ℕ}
    (M r δ : ℚ) (q f : Fin m → ℚ) :
    rationalNodupSortedViolation M r δ q f = rationalSortedViolation M r δ q f := by
  have hh : (fun l => rationalNodupPrefixLabels (rationalLabelSort f).1
      (rational_label_sort_nodup f) l) =
      (fun l => (((rationalLabelSort f).1.take l).map Prod.fst).toFinset) := by
    funext l
    exact rational_nodup_prefix_labels_eq _ _ l
  simp only [rationalNodupSortedViolation,rationalSortedViolation]
  rw [hh]

theorem rational_nodup_sorted_violation_none_iff {m : ℕ}
    (M r δ : ℚ) (q f : Fin m → ℚ) (hM : 0 ≤ M) (hq : ∀ i, 0 ≤ q i) :
    (rationalNodupSortedViolation M r δ q f).1 = none ↔
      ∀ S : Finset (Fin m),
        (∑ i ∈ S, (q i : ℝ)*(f i : ℝ))-
          (M : ℝ)*mass S (fun i => (q i : ℝ))*
            ((r : ℝ)-mass S (fun i => (q i : ℝ))) ≤ (δ : ℝ) := by
  rw [rational_nodup_sorted_violation_eq]
  exact rational_sorted_violation_none_iff_cuts M r δ q f hM hq

theorem rational_nodup_sorted_violation_some_sound {m : ℕ}
    (M r δ : ℚ) (q f : Fin m → ℚ) (S : Finset (Fin m))
    (hout : (rationalNodupSortedViolation M r δ q f).1 = some S) :
    (δ : ℝ) < (∑ i ∈ S, (q i : ℝ)*(f i : ℝ))-
      (M : ℝ)*mass S (fun i => (q i : ℝ))*
        ((r : ℝ)-mass S (fun i => (q i : ℝ))) := by
  rw [rational_nodup_sorted_violation_eq] at hout
  exact rational_sorted_violation_some_sound M r δ q f S hout

theorem rational_nodup_sorted_violation_comparisons {m : ℕ}
    (M r δ : ℚ) (q f : Fin m → ℚ) :
    (rationalNodupSortedViolation M r δ q f).2 ≤ m*(Nat.log2 m+2)+1 := by
  rw [rational_nodup_sorted_violation_eq]
  exact rational_sorted_violation_comparisons M r δ q f

end SparseCompletion
