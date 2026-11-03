module
public import Std
public section
namespace CyclicNormalization

theorem extract {α : Type} [DecidableEq α] (u l : List α)
    (hu : u.Nodup) (h : ∀ a ∈ u, a ∈ l) :
    ∃ t, l.Perm (u ++ t) := by
  induction u generalizing l with
  | nil => exact ⟨l, by simp⟩
  | cons a u ih =>
    have ha := h a (by simp)
    have hn := List.nodup_cons.mp hu
    have hs : ∀ b ∈ u, b ∈ l.erase a := by
      intro b hb
      apply (List.mem_erase_of_ne ?_).mpr (h b (by simp [hb]))
      intro he
      subst b
      exact hn.1 hb
    obtain ⟨t, ht⟩ := ih (l.erase a) hn.2 hs
    exact ⟨t, (List.perm_cons_erase ha).trans (List.Perm.cons a ht)⟩

@[expose] def residues : List (Fin 9) := [0,1,2,3,4,5,6,7,8]

theorem mem_residues (d : Fin 9) : d ∈ residues := by
  have h : ∀ d : Fin 9, d ∈ residues := by decide
  exact h d

theorem covered_ten_perm (l : List (Fin 9)) (hlen : l.length = 10)
    (hcover : ∀ d, d ∈ l) : ∃ d, l.Perm (residues ++ [d]) := by
  obtain ⟨t, ht⟩ := extract residues l (by decide) (fun a _ => hcover a)
  have hlen' := ht.length_eq
  have htlen : t.length = 1 := by simpa [residues, hlen] using hlen'
  cases t with
  | nil => simp at htlen
  | cons d t =>
    cases t with
    | nil => exact ⟨d, ht⟩
    | cons e t => simp at htlen

@[expose] def residueSum : List (Fin 9) → Nat
  | [] => 0
  | a :: l => a.val + residueSum l

theorem sum_perm {l t : List (Fin 9)} (h : l.Perm t) : residueSum l = residueSum t := by
  induction h with
  | nil => rfl
  | cons a h ih => simp [residueSum, ih]
  | swap a b l => simp [residueSum, Nat.add_comm, Nat.add_left_comm]
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem sum_residues_extra (d : Fin 9) : residueSum (residues ++ [d]) = 36 + d.val := by
  simp [residues, residueSum]
  omega

theorem covered_ten_sum_perm (l : List (Fin 9)) (hlen : l.length = 10)
    (hcover : ∀ d, d ∈ l) :
    l.Perm (residues ++ [⟨residueSum l % 9, Nat.mod_lt _ (by decide)⟩]) := by
  obtain ⟨d, hd⟩ := covered_ten_perm l hlen hcover
  have hs := sum_perm hd
  rw [sum_residues_extra] at hs
  have he : (⟨residueSum l % 9, Nat.mod_lt _ (by decide)⟩ : Fin 9) = d := by
    apply Fin.ext
    have := d.isLt
    simp only [Fin.val_mk]
    omega
  simpa [he] using hd

theorem count_residues (d : Fin 9) : residues.count d = 1 := by
  have := d.isLt
  match d with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ | ⟨8, _⟩ => decide +revert

theorem covered_ten_count (l : List (Fin 9)) (hlen : l.length = 10)
    (hcover : ∀ d, d ∈ l) (d : Fin 9) :
    l.count d = 1 + if d.val = residueSum l % 9 then 1 else 0 := by
  have hp := (covered_ten_sum_perm l hlen hcover).count_eq d
  rw [hp, List.count_append, count_residues]
  simp only [List.count_cons, List.count_nil, Nat.zero_add, beq_iff_eq]
  congr 1
  simp only [Fin.ext_iff]
  by_cases h : d.val = residueSum l % 9
  · simp [h]
  · have hn : residueSum l % 9 ≠ d.val := Ne.symm h
    simp [h, hn]

/-- The unique residue occurring twice is the total residue sum. -/
theorem repeated_iff_sum (l : List (Fin 9)) (hlen : l.length = 10)
    (hcover : ∀ d, d ∈ l) (d : Fin 9) :
    l.count d = 2 ↔ d.val = residueSum l % 9 := by
  rw [covered_ten_count l hlen hcover d]
  split <;> simp_all

theorem repeated_unique (l : List (Fin 9)) (hlen : l.length = 10)
    (hcover : ∀ d, d ∈ l) :
    ∃ d : Fin 9, l.count d = 2 ∧ ∀ e : Fin 9, l.count e = 2 → e = d := by
  refine ⟨⟨residueSum l % 9, Nat.mod_lt _ (by decide)⟩, ?_, ?_⟩
  · exact (repeated_iff_sum l hlen hcover _).mpr rfl
  · intro e he
    exact Fin.ext ((repeated_iff_sum l hlen hcover e).mp he)

/-- Modular subtraction by a fixed residue. -/
@[expose] def translate (d x : Fin 9) : Fin 9 :=
  ⟨(x.val + 9 - d.val) % 9, Nat.mod_lt _ (by decide)⟩

theorem translate_self (d : Fin 9) : translate d d = 0 := by
  apply Fin.ext
  simp [translate]

theorem translate_residues (d : Fin 9) :
    (residues.map (translate d)).Perm residues := by
  have h : ∀ d : Fin 9, (residues.map (translate d)).Perm residues := by decide
  exact h d

/-- Normalizing by the residue sum makes zero the unique repeated residue. -/
theorem covered_ten_normalize (l : List (Fin 9)) (hlen : l.length = 10)
    (hcover : ∀ d, d ∈ l) :
    (l.map (translate ⟨residueSum l % 9, Nat.mod_lt _ (by decide)⟩)).Perm
      (residues ++ [0]) := by
  let d : Fin 9 := ⟨residueSum l % 9, Nat.mod_lt _ (by decide)⟩
  have hd : l.Perm (residues ++ [d]) := covered_ten_sum_perm l hlen hcover
  have hp := hd.map (translate d)
  simp only [List.map_append, List.map_cons, List.map_nil, translate_self] at hp
  exact hp.trans ((translate_residues d).append_right [0])

/-- The list-level result applied to an arbitrary function of ten rows. -/
theorem ten_rows_normalize (f : Fin 10 → Fin 9) (hcover : ∀ d, ∃ r, f r = d) :
    ((List.ofFn f).map (translate
      ⟨residueSum (List.ofFn f) % 9, Nat.mod_lt _ (by decide)⟩)).Perm
      (residues ++ [0]) := by
  apply covered_ten_normalize
  · simp
  · intro d
    obtain ⟨r, hr⟩ := hcover d
    exact List.mem_ofFn.mpr ⟨r, hr⟩

theorem sum_translate (l : List (Fin 9)) (d : Fin 9) :
    (residueSum (l.map (translate d)) + l.length * d.val) % 9 = residueSum l % 9 := by
  induction l with
  | nil => simp [residueSum]
  | cons a l ih =>
    simp only [List.map_cons, residueSum, List.length_cons, Nat.succ_mul]
    have ha := a.isLt
    have hd := d.isLt
    simp only [translate, Fin.val_mk]
    omega

theorem normalize_sum_zero (l : List (Fin 9)) (hlen : l.length = 10) :
    residueSum (l.map (translate ⟨residueSum l % 9, Nat.mod_lt _ (by decide)⟩)) % 9 = 0 := by
  have h := sum_translate l ⟨residueSum l % 9, Nat.mod_lt _ (by decide)⟩
  simp only [hlen, Fin.val_mk] at h
  omega

/-- Sum of pointwise differences, expressed without integer subtraction. -/
theorem sum_difference {α : Type} (rows : List α) (f g : α → Fin 9) :
    (residueSum (rows.map (fun r => translate (g r) (f r))) +
      residueSum (rows.map g)) % 9 = residueSum (rows.map f) % 9 := by
  induction rows with
  | nil => simp [residueSum]
  | cons r rows ih =>
    simp only [List.map_cons, residueSum, translate, Fin.val_mk] at *
    have hf := (f r).isLt
    have hg := (g r).isLt
    omega

/-- A zero-sum covering difference list has exactly the standard normalized multiset. -/
theorem covered_ten_zero_sum (l : List (Fin 9)) (hlen : l.length = 10)
    (hcover : ∀ d, d ∈ l) (hsum : residueSum l % 9 = 0) :
    l.Perm (residues ++ [0]) := by
  have h := covered_ten_sum_perm l hlen hcover
  simpa [hsum] using h

#print axioms repeated_iff_sum
#print axioms repeated_unique
#print axioms covered_ten_perm
#print axioms covered_ten_sum_perm
#print axioms covered_ten_count
#print axioms covered_ten_normalize
#print axioms ten_rows_normalize
#print axioms sum_translate
#print axioms normalize_sum_zero
#print axioms sum_difference
#print axioms covered_ten_zero_sum
end CyclicNormalization
