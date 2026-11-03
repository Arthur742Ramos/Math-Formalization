module
public import CoveringNormalization
public import TransformSoundness
public import ArithmeticCertificate
public import ProfileEnumeration
public section
namespace CyclicRepresentativeExtension
open CyclicNormalization CoveringFormalRound3Linear

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem entry_lt : ∀ c : Fin 17, ∀ r : Fin 10, ∀ j : Fin 5,
    entry c.val r.val j.val < 9 := by decide

@[expose] def representative (c : Fin 17) (r : Fin 10) (j : Fin 5) : Fin 9 :=
  ⟨entry c.val r.val j.val, entry_lt c r j⟩

theorem first_column_zero : ∀ c : Fin 17, ∀ r : Fin 10,
    representative c r 0 = 0 := by decide

theorem column_sum_zero : ∀ c : Fin 17, ∀ j : Fin 5,
    residueSum (rows.map (fun r => representative c r j)) % 9 = 0 := by decide

@[expose] def normalized (x : Fin 10 → Fin 9) (r : Fin 10) : Fin 9 :=
  translate ⟨residueSum (rows.map x) % 9, Nat.mod_lt _ (by decide)⟩ (x r)

theorem normalized_sum (x : Fin 10 → Fin 9) :
    residueSum (rows.map (normalized x)) % 9 = 0 := by
  have h := normalize_sum_zero (rows.map x) (by simp [rows])
  unfold normalized
  simpa only [List.map_map, Function.comp_def] using h

theorem normalize_extension {C : Type} (m : Fin 10 → C → Fin 9)
    (x : Fin 10 → Fin 9) (h : CoveringTransforms.Extends m x) :
    CoveringTransforms.Extends m (normalized x) := by
  intro j d
  let s : Fin 9 := ⟨residueSum (rows.map x) % 9, Nat.mod_lt _ (by decide)⟩
  obtain ⟨e, he⟩ := translate_surjective s d
  obtain ⟨r, hr⟩ := h j e
  refine ⟨r, ?_⟩
  have hx := (x r).isLt
  have hm := (m r j).isLt
  have hs := s.isLt
  have hd := d.isLt
  have he' := congrArg Fin.val he
  have hr' := congrArg Fin.val hr
  apply Fin.ext
  change (((x r).val + 9 - s.val) % 9 + 9 - (m r j).val) % 9 = d.val
  simp only [translate, CoveringTransforms.difference, Fin.val_mk] at he' hr'
  omega

theorem extension_difference_perm (c : Fin 17) (x : Fin 10 → Fin 9)
    (h : CoveringTransforms.Extends (representative c) x) (j : Fin 5) :
    (rows.map (fun r => translate (representative c r j) (normalized x r))).Perm
      (residues ++ [0]) := by
  apply covered_ten_zero_sum
  · simp [rows]
  · intro d
    obtain ⟨r, hr⟩ := normalize_extension (representative c) x h j d
    exact List.mem_map.mpr ⟨r, List.mem_ofFn.mpr ⟨r,rfl⟩, hr⟩
  · have hs := sum_difference rows (normalized x) (fun r => representative c r j)
    have hz := normalized_sum x
    have hm := column_sum_zero c j
    omega

theorem extension_column_perm (c : Fin 17) (x : Fin 10 → Fin 9)
    (h : CoveringTransforms.Extends (representative c) x) :
    (rows.map (normalized x)).Perm (residues ++ [0]) := by
  have hp := extension_difference_perm c x h 0
  have hz : ∀ a : Fin 9, translate 0 a = a := by decide
  simpa only [first_column_zero, hz] using hp

@[expose] def low (a : Fin 9) : CoveringProfiles.Trit := ⟨a.val % 3, Nat.mod_lt _ (by decide)⟩
@[expose] def high (a : Fin 9) : CoveringProfiles.Trit := ⟨a.val / 3, by have := a.isLt; omega⟩

theorem count_perm {a b : List CoveringProfiles.Trit} (h : a.Perm b) (d : CoveringProfiles.Trit) :
    CoveringProfiles.count d a = CoveringProfiles.count d b := by
  induction h with
  | nil => rfl
  | cons x h ih => simp [CoveringProfiles.count, ih]
  | swap x y l => simp [CoveringProfiles.count, Nat.add_comm, Nat.add_left_comm]
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem normalized_lower_quotas {l : List (Fin 9)} (h : l.Perm (residues ++ [0])) :
    CoveringProfiles.count 0 (l.map low) = 4 ∧
    CoveringProfiles.count 1 (l.map low) = 3 ∧
    CoveringProfiles.count 2 (l.map low) = 3 := by
  have hp := h.map low
  rw [count_perm hp 0, count_perm hp 1, count_perm hp 2]
  decide

theorem nat_sum_perm {a b : List Nat} (h : a.Perm b) : a.sum = b.sum := by
  induction h with
  | nil => rfl
  | cons x h ih => simp [ih]
  | swap x y l => simp [Nat.add_comm, Nat.add_left_comm]
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

/-- The exact first and second moments of every normalized residue fibre. -/
theorem normalized_fiber_moments {l : List (Fin 9)}
    (h : l.Perm (residues ++ [0])) (t : Fin 3) :
    ((l.filter (fun a => low a == t)).map (fun (a : Fin 9) => a.val / 3)).sum % 3 = 0 ∧
    ((l.filter (fun a => low a == t)).map (fun (a : Fin 9) => (a.val / 3) * (a.val / 3))).sum % 3 = 2 := by
  have hp := h.filter (fun a => low a == t)
  rw [nat_sum_perm (hp.map (fun (a : Fin 9) => a.val / 3)),
    nat_sum_perm (hp.map (fun (a : Fin 9) => (a.val / 3) * (a.val / 3)))]
  have hc : ∀ t : Fin 3,
      (((residues ++ [0]).filter (fun a => low a == t)).map (fun (a : Fin 9) => a.val / 3)).sum % 3 = 0 ∧
      (((residues ++ [0]).filter (fun a => low a == t)).map (fun (a : Fin 9) => (a.val / 3) * (a.val / 3))).sum % 3 = 2 := by decide
  exact hc t

/-- Conditional-sum form of fibre moments, convenient for the F3 equations. -/
theorem normalized_conditional_moments {l : List (Fin 9)}
    (h : l.Perm (residues ++ [0])) (t : Fin 3) :
    (l.map (fun a => if low a = t then a.val / 3 else 0)).sum % 3 = 0 ∧
    (l.map (fun a => if low a = t then (a.val / 3) * (a.val / 3) else 0)).sum % 3 = 2 := by
  rw [nat_sum_perm (h.map (fun a => if low a = t then a.val / 3 else 0)),
    nat_sum_perm (h.map (fun a => if low a = t then (a.val / 3) * (a.val / 3) else 0))]
  have hc : ∀ t : Fin 3,
      ((residues ++ [0]).map (fun a => if low a = t then a.val / 3 else 0)).sum % 3 = 0 ∧
      ((residues ++ [0]).map (fun a => if low a = t then (a.val / 3) * (a.val / 3) else 0)).sum % 3 = 2 := by decide
  exact hc t

#print axioms normalized_fiber_moments
#print axioms normalized_conditional_moments
#print axioms extension_difference_perm
#print axioms extension_column_perm
#print axioms normalized_lower_quotas
end CyclicRepresentativeExtension
