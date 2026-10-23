/- AI-assisted formalization under the repository Apache-2.0 license.
The computed sorted table supplies a bijective reindexing of original labels. -/
module
public import ProtectedSources.RationalLabelSort
@[expose] public section
namespace SparseCompletion

def rationalSortedIndex {m : ℕ} (f : Fin m → ℚ)
    (i : Fin (rationalLabelSort f).1.length) : Fin m :=
  ((rationalLabelSort f).1.get i).1

theorem rational_sorted_index_score {m : ℕ} (f : Fin m → ℚ)
    (i : Fin (rationalLabelSort f).1.length) :
    ((rationalLabelSort f).1.get i).2 = f (rationalSortedIndex f i) :=
  rational_label_sort_stored_score f _ (List.get_mem _ _)

theorem rational_sorted_index_injective {m : ℕ} (f : Fin m → ℚ) :
    Function.Injective (rationalSortedIndex f) := by
  intro i j hij
  have hn := List.Nodup.of_map Prod.fst (rational_label_sort_nodup f)
  apply hn.get_inj_iff.mp
  apply Prod.ext hij
  rw [rational_sorted_index_score, rational_sorted_index_score, hij]

theorem rational_sorted_index_surjective {m : ℕ} (f : Fin m → ℚ) :
    Function.Surjective (rationalSortedIndex f) := by
  intro i
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp (rational_label_sort_covers f i)
  exact ⟨j, congrArg Prod.fst hj⟩

theorem rational_sorted_index_bijective {m : ℕ} (f : Fin m → ℚ) :
    Function.Bijective (rationalSortedIndex f) :=
  ⟨rational_sorted_index_injective f, rational_sorted_index_surjective f⟩

theorem rational_sorted_index_antitone {m : ℕ} (f : Fin m → ℚ) :
    Antitone (fun i => f (rationalSortedIndex f i)) := by
  simpa only [← rational_sorted_index_score] using rational_label_sort_index_antitone f

noncomputable def rationalSortedEquiv {m : ℕ} (f : Fin m → ℚ) :
    Fin (rationalLabelSort f).1.length ≃ Fin m :=
  Equiv.ofBijective (rationalSortedIndex f) (rational_sorted_index_bijective f)

end SparseCompletion
