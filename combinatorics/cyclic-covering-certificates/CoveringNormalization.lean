module
public import Normalization
public import BaseWitnesses
public section
namespace CyclicNormalization

@[expose] def rows : List (Fin 10) := List.ofFn id

@[expose] def columnSum {k : Nat} (m : Fin 10 → Fin k → Fin 9) (c : Fin k) : Fin 9 :=
  ⟨residueSum (rows.map (fun r => m r c)) % 9, Nat.mod_lt _ (by decide)⟩

@[expose] def normalizeColumns {k : Nat} (m : Fin 10 → Fin k → Fin 9) :
    Fin 10 → Fin k → Fin 9 := fun r c => translate (columnSum m c) (m r c)

theorem translate_surjective (d y : Fin 9) : ∃ x, translate d x = y := by
  refine ⟨⟨(y.val + d.val) % 9, Nat.mod_lt _ (by decide)⟩, ?_⟩
  apply Fin.ext
  simp only [translate, Fin.val_mk]
  have := d.isLt
  have := y.isLt
  omega

theorem translate_difference (a b sa sb : Fin 9) :
    translate (translate sb b) (translate sa a) =
    translate (translate sb sa) (translate b a) := by
  apply Fin.ext
  simp only [translate, Fin.val_mk]
  have := a.isLt
  have := b.isLt
  have := sa.isLt
  have := sb.isLt
  omega

theorem normalize_preserves_covers {k : Nat} (m : Fin 10 → Fin k → Fin 9)
    (h : CoveringScheme.Covers 9 10 k m) :
    CoveringScheme.Covers 9 10 k (normalizeColumns m) := by
  intro a b hab d
  obtain ⟨x, hx⟩ := translate_surjective (translate (columnSum m b) (columnSum m a)) d
  obtain ⟨r, hr⟩ := h a b hab x
  refine ⟨r, ?_⟩
  have hr' : translate (m r b) (m r a) = x := Fin.ext hr
  have ht := translate_difference (m r a) (m r b) (columnSum m a) (columnSum m b)
  rw [hr', hx] at ht
  exact congrArg Fin.val ht

theorem normalized_column_sum_zero {k : Nat} (m : Fin 10 → Fin k → Fin 9) (c : Fin k) :
    residueSum (rows.map (fun r => normalizeColumns m r c)) % 9 = 0 := by
  have h := normalize_sum_zero (rows.map (fun r => m r c)) (by simp [rows])
  simpa [List.map_map, normalizeColumns, columnSum, Function.comp_def] using h

/-- Every pair in an arbitrary covering 10-row array can be normalized simultaneously:
    its difference list contains zero twice and every nonzero residue once. -/
theorem normalized_pair_perm {k : Nat} (m : Fin 10 → Fin k → Fin 9)
    (h : CoveringScheme.Covers 9 10 k m) (a b : Fin k) (hab : a ≠ b) :
    (rows.map (fun r => translate (normalizeColumns m r b) (normalizeColumns m r a))).Perm
      (residues ++ [0]) := by
  apply covered_ten_zero_sum
  · simp [rows]
  · intro d
    obtain ⟨r, hr⟩ := normalize_preserves_covers m h a b hab d
    apply List.mem_map.mpr
    refine ⟨r, ?_, Fin.ext hr⟩
    exact List.mem_ofFn.mpr ⟨r, rfl⟩
  · have hs := sum_difference rows (fun r => normalizeColumns m r a)
      (fun r => normalizeColumns m r b)
    have ha := normalized_column_sum_zero m a
    have hb := normalized_column_sum_zero m b
    omega

#print axioms normalize_preserves_covers
#print axioms normalized_column_sum_zero
#print axioms normalized_pair_perm
end CyclicNormalization
