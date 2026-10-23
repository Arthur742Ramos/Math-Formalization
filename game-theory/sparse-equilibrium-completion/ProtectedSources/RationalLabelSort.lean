/- AI-assisted formalization under the repository Apache-2.0 license.
Finite rational score sorting retains every original action label exactly once. -/
module
public import ProtectedSources.RationalScoreSort
@[expose] public section
namespace SparseCompletion

def rationalLabelSort {m : ℕ} (f : Fin m → ℚ) : List (Fin m × ℚ) × ℕ :=
  rationalScoreSort ((List.finRange m).map (fun i => (i, f i)))

theorem rational_label_sort_length {m : ℕ} (f : Fin m → ℚ) :
    (rationalLabelSort f).1.length = m := by
  simp only [rationalLabelSort, rational_score_sort_length, List.length_map, List.length_finRange]

theorem rational_label_sort_labels {m : ℕ} (f : Fin m → ℚ) :
    ((rationalLabelSort f).1.map Prod.fst).Perm (List.finRange m) := by
  have h := (rational_score_sort_perm ((List.finRange m).map (fun i => (i, f i)))).map Prod.fst
  simpa only [rationalLabelSort, List.map_map, Function.comp_def, List.map_id'] using h

theorem rational_label_sort_nodup {m : ℕ} (f : Fin m → ℚ) :
    ((rationalLabelSort f).1.map Prod.fst).Nodup :=
  (rational_label_sort_labels f).nodup_iff.mpr (List.nodup_finRange m)

theorem rational_label_sort_stored_score {m : ℕ} (f : Fin m → ℚ) :
    ∀ a ∈ (rationalLabelSort f).1, a.2 = f a.1 := by
  apply rational_score_sort_stored_score
  intro a ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  rfl

theorem rational_label_sort_descending {m : ℕ} (f : Fin m → ℚ) :
    (rationalLabelSort f).1.Pairwise (fun a b => b.2 ≤ a.2) :=
  rational_score_sort_descending _

theorem rational_label_sort_comparisons {m : ℕ} (f : Fin m → ℚ) :
    (rationalLabelSort f).2 ≤ m * (Nat.log2 m + 1) := by
  simpa only [rationalLabelSort, List.length_map, List.length_finRange] using
    rational_score_sort_comparisons ((List.finRange m).map (fun i => (i, f i)))

theorem rational_label_sort_covers {m : ℕ} (f : Fin m → ℚ) (i : Fin m) :
    (i, f i) ∈ (rationalLabelSort f).1 := by
  apply (rational_score_sort_perm _).mem_iff.mpr
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

theorem rational_label_sort_index_antitone {m : ℕ} (f : Fin m → ℚ) :
    Antitone (fun i : Fin (rationalLabelSort f).1.length =>
      ((rationalLabelSort f).1.get i).2) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hlt | heq
  · simpa only [List.get_eq_getElem] using
      (rational_label_sort_descending f).rel_getElem_of_lt i.isLt j.isLt hlt
  · rw [heq]

end SparseCompletion
