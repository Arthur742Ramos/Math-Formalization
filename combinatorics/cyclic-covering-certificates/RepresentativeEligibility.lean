module
public import RepresentativeExtension
public import ProfileCoverage
public section
namespace CyclicRepresentativeExtension
open CyclicNormalization CoveringProfiles CoveringProfileData CoveringProfileCoverage
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem literal_lower_columns : ∀ c : Fin 17,
    lowerColumns.getD c.val [] = List.ofFn (fun j : Fin 5 =>
      rows.map (fun r => low (representative c r j))) := by decide

theorem low_difference : ∀ a b : Fin 9,
    (low (translate b a)).val = ((low a).val + 3 - (low b).val) % 3 := by decide

theorem histogram_map_val (xs : List Trit) :
    histogram (xs.map Fin.val) = (count 0 xs, count 1 xs, count 2 xs) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rcases trit_cases a with rfl | rfl | rfl
    all_goals simp [histogram, count, ih, Nat.add_comm]

theorem normalized_histogram {l : List (Fin 9)} (h : l.Perm (residues ++ [0])) :
    histogram (l.map (fun a => (low a).val)) = (4,3,3) := by
  have hq := normalized_lower_quotas h
  have hh := histogram_map_val (l.map low)
  simpa [List.map_map, Function.comp_def, hq.1, hq.2.1, hq.2.2] using hh

theorem zipWith_maps {α β γ δ : Type} (f : α → β) (g : α → γ)
    (op : β → γ → δ) (l : List α) :
    List.zipWith op (l.map f) (l.map g) = l.map (fun a => op (f a) (g a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem extension_columnOK (c : Fin 17) (x : Fin 10 → Fin 9)
    (h : CoveringTransforms.Extends (representative c) x) (j : Fin 5) :
    columnOK (rows.map (fun r => low (normalized x r)))
      (rows.map (fun r => low (representative c r j))) = true := by
  apply decide_eq_true
  rw [zipWith_maps]
  have hh := normalized_histogram (extension_difference_perm c x h j)
  simpa only [List.map_map, Function.comp_def, low_difference] using hh

theorem extension_eligible (c : Fin 17) (x : Fin 10 → Fin 9)
    (h : CoveringTransforms.Extends (representative c) x) :
    Eligible c.val (rows.map (fun r => low (normalized x r))) := by
  have hq := normalized_lower_quotas (extension_column_perm c x h)
  simp only [List.map_map, Function.comp_def] at hq
  refine ⟨by simp [rows], hq.1, hq.2.1, hq.2.2, ?_⟩
  unfold profileOK
  rw [literal_lower_columns]
  apply List.all_eq_true.mpr
  intro col hc
  have hm := List.mem_of_mem_drop hc
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hm
  exact extension_columnOK c x h j

#print axioms extension_eligible
end CyclicRepresentativeExtension
