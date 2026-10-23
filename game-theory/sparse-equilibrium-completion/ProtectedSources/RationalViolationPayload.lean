/- AI-assisted formalization under the repository Apache-2.0 license.
The executable payload uses one cached sorted table. The counter excludes
finite-set construction, arithmetic, indexing, bit operations and runtime. -/
module
public import ProtectedSources.RationalViolationSearch
public import ProtectedSources.RationalSortedCutCheck
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalSortedViolation {m : ℕ} (M r δ : ℚ) (q f : Fin m → ℚ) :
    Option (Finset (Fin m)) × ℕ :=
  let sorted := rationalLabelSort f
  let scan := rationalViolationSearch M r δ 0 0
    (sorted.1.map (fun a => (q a.1, q a.1*a.2)))
  (scan.1.map (fun l => ((sorted.1.take l).map Prod.fst).toFinset), sorted.2+scan.2)

theorem rational_nodup_toFinset_sum {α β : Type*} [DecidableEq α]
    [AddCommMonoid β] (xs : List α) (hn : xs.Nodup) (g : α → β) :
    (∑ i ∈ xs.toFinset, g i) = (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hn
    simp [ha, ih ht]

theorem rational_sorted_prefix_sum {m : ℕ} (f : Fin m → ℚ) (l : ℕ)
    (g : Fin m → ℚ) :
    (∑ i ∈ (((rationalLabelSort f).1.take l).map Prod.fst).toFinset, g i) =
      (((rationalLabelSort f).1.take l).map (fun a => g a.1)).sum := by
  have hn : (((rationalLabelSort f).1.take l).map Prod.fst).Nodup := by
    rw [List.map_take]
    exact (rational_label_sort_nodup f).take
  rw [rational_nodup_toFinset_sum _ hn]
  simp only [List.map_map, Function.comp_def]

theorem rational_sorted_violation_none_iff_check {m : ℕ}
    (M r δ : ℚ) (q f : Fin m → ℚ) :
    (rationalSortedViolation M r δ q f).1 = none ↔
      (rationalSortedCutCheck M r δ q f).1 = true := by
  change Option.map _ _ = none ↔ _
  rw [Option.map_eq_none_iff]
  exact rational_violation_search_none_iff M r δ 0 0 _

theorem rational_sorted_violation_count {m : ℕ}
    (M r δ : ℚ) (q f : Fin m → ℚ) :
    (rationalSortedViolation M r δ q f).2 =
      (rationalSortedCutCheck M r δ q f).2 := by
  change (rationalLabelSort f).2+_ = (rationalLabelSort f).2+_
  rw [rational_violation_search_count]

theorem rational_sorted_violation_comparisons {m : ℕ}
    (M r δ : ℚ) (q f : Fin m → ℚ) :
    (rationalSortedViolation M r δ q f).2 ≤ m*(Nat.log2 m+2)+1 := by
  rw [rational_sorted_violation_count]
  exact rational_sorted_cut_check_comparisons M r δ q f

theorem rational_sorted_violation_none_iff_cuts {m : ℕ}
    (M r δ : ℚ) (q f : Fin m → ℚ) (hM : 0 ≤ M) (hq : ∀ i, 0 ≤ q i) :
    (rationalSortedViolation M r δ q f).1 = none ↔
      ∀ S : Finset (Fin m),
        (∑ i ∈ S, (q i : ℝ)*(f i : ℝ))-
          (M : ℝ)*mass S (fun i => (q i : ℝ))*
            ((r : ℝ)-mass S (fun i => (q i : ℝ))) ≤ (δ : ℝ) :=
  (rational_sorted_violation_none_iff_check M r δ q f).trans
    (rational_sorted_cut_check_iff M r δ q f hM hq)

theorem rational_sorted_violation_some_sound {m : ℕ}
    (M r δ : ℚ) (q f : Fin m → ℚ) (S : Finset (Fin m))
    (hout : (rationalSortedViolation M r δ q f).1 = some S) :
    (δ : ℝ) < (∑ i ∈ S, (q i : ℝ)*(f i : ℝ))-
      (M : ℝ)*mass S (fun i => (q i : ℝ))*
        ((r : ℝ)-mass S (fun i => (q i : ℝ))) := by
  change Option.map _ _ = some S at hout
  obtain ⟨l, hl, hS⟩ := Option.map_eq_some_iff.mp hout
  obtain ⟨_, hbad⟩ := rational_violation_search_some_sound M r δ 0 0
    ((rationalLabelSort f).1.map (fun a => (q a.1,q a.1*a.2))) l hl
  simp only [← List.map_take, List.map_map, Function.comp_def, zero_add] at hbad
  have hm : (((rationalLabelSort f).1.take l).map (fun a => q a.1*a.2)) =
      (((rationalLabelSort f).1.take l).map (fun a => q a.1*f a.1)) := by
    apply List.map_congr_left
    intro a ha
    rw [rational_label_sort_stored_score f a (List.mem_of_mem_take ha)]
  rw [hm, ← rational_sorted_prefix_sum f l (fun i => q i*f i),
    ← rational_sorted_prefix_sum f l q] at hbad
  rw [hS] at hbad
  dsimp only [mass]
  exact_mod_cast hbad

end SparseCompletion
