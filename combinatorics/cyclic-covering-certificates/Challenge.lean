module
public import Std
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
/- Self-contained fixed-representative nonextension theorem.
   Only the seventeen literal representatives are quantified over.
   This file does not assert global classification completeness. -/


-- Normalization
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
@[expose] def translate (d x : Fin 9) : Fin 9 :=
  ⟨(x.val + 9 - d.val) % 9, Nat.mod_lt _ (by decide)⟩
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
theorem covered_ten_zero_sum (l : List (Fin 9)) (hlen : l.length = 10)
    (hcover : ∀ d, d ∈ l) (hsum : residueSum l % 9 = 0) :
    l.Perm (residues ++ [0]) := by
  have h := covered_ten_sum_perm l hlen hcover
  simpa [hsum] using h
end CyclicNormalization


-- CoveringNormalization
namespace CyclicNormalization
@[expose] def rows : List (Fin 10) := List.ofFn id
theorem translate_surjective (d y : Fin 9) : ∃ x, translate d x = y := by
  refine ⟨⟨(y.val + d.val) % 9, Nat.mod_lt _ (by decide)⟩, ?_⟩
  apply Fin.ext
  simp only [translate, Fin.val_mk]
  have := d.isLt
  have := y.isLt
  omega
end CyclicNormalization


-- TransformSoundness
namespace CoveringTransforms
/-- A named bound keeps the elaborated definition independent of proof-cache context. -/
theorem difference_lt (a b : Fin 9) : (b.val + 9 - a.val) % 9 < 9 :=
  Nat.mod_lt _ (by decide)

@[expose] def difference (a b : Fin 9) : Fin 9 :=
  ⟨(b.val + 9 - a.val) % 9, difference_lt a b⟩
@[expose] def Extends {R C : Type} (array : R → C → Fin 9) (newColumn : R → Fin 9) : Prop :=
  ∀ j d, ∃ r, difference (array r j) (newColumn r) = d
end CoveringTransforms


-- F3Linear
namespace CoveringF3
abbrev F3 := Fin 3
@[expose] def ofNat (n : Nat) : F3 := ⟨n % 3, Nat.mod_lt _ (by decide)⟩
@[expose] def add (a b : F3) : F3 := ofNat (a.val + b.val)
@[expose] def mul (a b : F3) : F3 := ofNat (a.val * b.val)
theorem add_assoc : ∀ a b c : F3, add (add a b) c = add a (add b c) := by decide

theorem add_zero : ∀ a : F3, add a 0 = a := by decide
theorem zero_add : ∀ a : F3, add 0 a = a := by decide
theorem mul_zero : ∀ a : F3, mul a 0 = 0 := by decide
theorem zero_mul : ∀ a : F3, mul 0 a = 0 := by decide
theorem mul_assoc : ∀ a b c : F3, mul a (mul b c) = mul (mul a b) c := by decide
theorem mul_add : ∀ a b c : F3, mul a (add b c) = add (mul a b) (mul a c) := by decide
theorem add_mul : ∀ a b c : F3, mul (add a b) c = add (mul a c) (mul b c) := by decide
theorem add_interchange : ∀ a b c d : F3,
    add (add a b) (add c d) = add (add a c) (add b d) := by decide

@[expose] def sum : Nat → (Nat → F3) → F3
  | 0, _ => 0
  | n+1, f => add (sum n f) (f n)
theorem sum_congr (n : Nat) (f g : Nat → F3)
    (h : ∀ i, i < n → f i = g i) : sum n f = sum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sum]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]
theorem sum_zero (n : Nat) : sum n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sum, ih, add_zero]
theorem sum_add (n : Nat) (f g : Nat → F3) :
    sum n (fun i => add (f i) (g i)) = add (sum n f) (sum n g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sum, ih]
    exact add_interchange _ _ _ _
theorem mul_sum (n : Nat) (a : F3) (f : Nat → F3) :
    mul a (sum n f) = sum n (fun i => mul a (f i)) := by
  induction n with
  | zero => exact mul_zero a
  | succ n ih => simp only [sum, mul_add, ih]
theorem sum_mul (n : Nat) (f : Nat → F3) (a : F3) :
    mul (sum n f) a = sum n (fun i => mul (f i) a) := by
  induction n with
  | zero => exact zero_mul a
  | succ n ih => simp only [sum, add_mul, ih]
theorem sum_swap (m n : Nat) (f : Nat → Nat → F3) :
    sum m (fun i => sum n (f i)) = sum n (fun j => sum m (fun i => f i j)) := by
  induction m with
  | zero => simp only [sum, sum_zero]
  | succ m ih => simp only [sum, ih, sum_add]
theorem weighted_matrix_sum (m n : Nat) (A : Nat → Nat → F3)
    (v w : Nat → F3) :
    sum m (fun r => mul (w r) (sum n (fun c => mul (A r c) (v c)))) =
    sum n (fun c => mul (sum m (fun r => mul (w r) (A r c))) (v c)) := by
  calc
    _ = sum m (fun r => sum n (fun c => mul (w r) (mul (A r c) (v c)))) :=
      sum_congr m _ _ (fun r _ => mul_sum n _ _)
    _ = sum n (fun c => sum m (fun r => mul (w r) (mul (A r c) (v c)))) :=
      sum_swap m n _
    _ = sum n (fun c => sum m (fun r => mul (mul (w r) (A r c)) (v c))) :=
      sum_congr n _ _ (fun c _ => sum_congr m _ _ (fun r _ => mul_assoc _ _ _))
    _ = _ := sum_congr n _ _ (fun c _ => (sum_mul m _ _).symm)

theorem left_nullspace_sound (m n : Nat) (A : Nat → Nat → F3)
    (b w : Nat → F3)
    (hA : ∀ c, c < n → sum m (fun r => mul (w r) (A r c)) = 0)
    (hb : sum m (fun r => mul (w r) (b r)) = 1) :
    ¬ ∃ v : Nat → F3, ∀ r, r < m → sum n (fun c => mul (A r c) (v c)) = b r := by
  rintro ⟨v, hv⟩
  have hz : sum m (fun r => mul (w r) (sum n (fun c => mul (A r c) (v c)))) = 0 := by
    rw [weighted_matrix_sum]
    calc
      _ = sum n (fun _ => 0) := sum_congr n _ _ (fun c hc => by rw [hA c hc, zero_mul])
      _ = 0 := sum_zero n
  have ho : sum m (fun r => mul (w r) (sum n (fun c => mul (A r c) (v c)))) = 1 := by
    calc
      _ = sum m (fun r => mul (w r) (b r)) :=
        sum_congr m _ _ (fun r hr => by rw [hv r hr])
      _ = 1 := hb
  exact (by decide : (0 : F3) ≠ 1) (hz.symm.trans ho)
@[expose] def neg (a : F3) : F3 := ofNat (3-a.val)
theorem mul_one : ∀ a : F3, mul 1 a = a := by decide
theorem recover_affine : ∀ a b d t : F3,
    add a (mul (neg d) t) = b → a = add b (mul d t) := by decide

theorem sum_single (n k : Nat) (hk : k < n) (a : F3) :
    sum n (fun c => if c = k then a else 0) = a := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hkn : k = n
    · subst k
      simp only [sum, if_pos rfl]
      have hz : sum n (fun c => if c = n then a else 0) = 0 := by
        calc
          _ = sum n (fun _ => 0) := sum_congr n _ _ (fun c hc => by simp [show c ≠ n by omega])
          _ = 0 := sum_zero n
      rw [hz, zero_add]
      simp
    · have hlt : k < n := by omega
      simp only [sum, ih hlt, if_neg (Ne.symm hkn), add_zero]

@[expose] def affineRow (j f : Nat) (d : F3) (c : Nat) : F3 :=
  add (if c = j then 1 else 0) (if c = f then neg d else 0)
theorem sum_affine_row (n j f : Nat) (hj : j < n) (hf : f < n)
    (d : F3) (v : Nat → F3) :
    sum n (fun c => mul (affineRow j f d c) (v c)) =
      add (v j) (mul (neg d) (v f)) := by
  calc
    _ = sum n (fun c => add
        (if c = j then v j else 0)
        (if c = f then mul (neg d) (v f) else 0)) := by
      apply sum_congr n
      intro c hc
      unfold affineRow
      rw [add_mul]
      have hleft : mul (if c = j then 1 else 0) (v c) = (if c = j then v j else 0) := by
        by_cases h : c = j
        · subst c; simp [mul_one]
        · simp [h, zero_mul]
      have hright : mul (if c = f then neg d else 0) (v c) =
          (if c = f then mul (neg d) (v f) else 0) := by
        by_cases h : c = f
        · subst c; simp
        · simp [h, zero_mul]
      rw [hleft, hright]
    _ = add (sum n (fun c => if c = j then v j else 0))
      (sum n (fun c => if c = f then mul (neg d) (v f) else 0)) := sum_add n _ _
    _ = _ := by rw [sum_single n j hj, sum_single n f hf]
theorem certified_consequence (m n : Nat) (A : Nat → Nat → F3)
    (b w target v : Nat → F3) (right : F3)
    (hA : ∀ c, c < n → sum m (fun r => mul (w r) (A r c)) = target c)
    (hb : sum m (fun r => mul (w r) (b r)) = right)
    (hv : ∀ r, r < m → sum n (fun c => mul (A r c) (v c)) = b r) :
    sum n (fun c => mul (target c) (v c)) = right := by
  calc
    _ = sum n (fun c => mul (sum m (fun r => mul (w r) (A r c))) (v c)) :=
      sum_congr n _ _ (fun c hc => by rw [hA c hc])
    _ = sum m (fun r => mul (w r) (sum n (fun c => mul (A r c) (v c)))) :=
      (weighted_matrix_sum m n A v w).symm
    _ = sum m (fun r => mul (w r) (b r)) :=
      sum_congr m _ _ (fun r hr => by rw [hv r hr])
    _ = right := hb
end CoveringF3


-- ArithmeticCertificate
namespace CoveringFormalRound3Linear
@[expose] def representatives : List (List (List Nat)) := [
  [[0, 0, 0, 1, 1], [0, 0, 1, 0, 7], [0, 1, 0, 7, 0], [0, 2, 5, 5, 4], [0, 3, 7, 3, 0], [0, 4, 4, 8, 8], [0, 5, 2, 4, 5], [0, 6, 8, 2, 6], [0, 7, 3, 0, 3], [0, 8, 6, 6, 2]],
  [[0, 0, 0, 1, 1], [0, 0, 1, 5, 6], [0, 1, 3, 3, 0], [0, 2, 2, 0, 4], [0, 3, 8, 7, 3], [0, 4, 7, 4, 7], [0, 5, 0, 2, 0], [0, 6, 4, 0, 2], [0, 7, 6, 6, 5], [0, 8, 5, 8, 8]],
  [[0, 0, 0, 1, 1], [0, 0, 3, 0, 8], [0, 1, 5, 3, 5], [0, 2, 4, 6, 2], [0, 3, 0, 8, 0], [0, 4, 2, 2, 6], [0, 5, 1, 5, 3], [0, 6, 6, 0, 0], [0, 7, 8, 4, 7], [0, 8, 7, 7, 4]],
  [[0, 0, 0, 1, 1], [0, 0, 3, 0, 8], [0, 1, 5, 5, 3], [0, 2, 4, 2, 6], [0, 3, 0, 8, 0], [0, 4, 2, 6, 2], [0, 5, 1, 3, 5], [0, 6, 6, 0, 0], [0, 7, 8, 4, 7], [0, 8, 7, 7, 4]],
  [[0, 0, 0, 1, 1], [0, 0, 4, 0, 7], [0, 1, 1, 5, 5], [0, 2, 8, 8, 4], [0, 3, 5, 2, 3], [0, 4, 0, 7, 0], [0, 5, 3, 3, 2], [0, 6, 7, 6, 0], [0, 7, 6, 0, 6], [0, 8, 2, 4, 8]],
  [[0, 0, 0, 1, 1], [0, 0, 5, 0, 8], [0, 1, 7, 5, 7], [0, 2, 2, 4, 4], [0, 3, 4, 0, 3], [0, 4, 3, 3, 0], [0, 5, 0, 8, 0], [0, 6, 8, 2, 6], [0, 7, 1, 7, 5], [0, 8, 6, 6, 2]],
  [[0, 0, 0, 1, 1], [0, 0, 6, 2, 3], [0, 1, 1, 0, 0], [0, 2, 3, 0, 6], [0, 3, 2, 6, 0], [0, 4, 8, 8, 4], [0, 5, 7, 5, 7], [0, 6, 0, 3, 2], [0, 7, 5, 7, 5], [0, 8, 4, 4, 8]],
  [[0, 0, 0, 1, 1], [0, 0, 8, 2, 2], [0, 1, 1, 0, 6], [0, 2, 5, 0, 5], [0, 3, 7, 7, 0], [0, 4, 6, 4, 3], [0, 5, 2, 8, 0], [0, 6, 4, 6, 4], [0, 7, 3, 3, 7], [0, 8, 0, 5, 8]],
  [[0, 0, 0, 1, 1], [0, 0, 8, 2, 5], [0, 1, 1, 0, 0], [0, 2, 5, 0, 8], [0, 3, 7, 7, 3], [0, 4, 6, 4, 6], [0, 5, 2, 8, 0], [0, 6, 4, 6, 4], [0, 7, 3, 3, 7], [0, 8, 0, 5, 2]],
  [[0, 0, 0, 1, 1], [0, 0, 8, 2, 8], [0, 1, 1, 0, 3], [0, 2, 5, 0, 2], [0, 3, 7, 7, 6], [0, 4, 6, 4, 0], [0, 5, 2, 8, 0], [0, 6, 4, 6, 4], [0, 7, 3, 3, 7], [0, 8, 0, 5, 5]],
  [[0, 0, 0, 1, 2], [0, 0, 1, 0, 4], [0, 1, 0, 0, 8], [0, 2, 6, 4, 1], [0, 3, 5, 8, 6], [0, 4, 2, 7, 0], [0, 5, 8, 5, 5], [0, 6, 3, 3, 3], [0, 7, 7, 2, 7], [0, 8, 4, 6, 0]],
  [[0, 0, 0, 1, 2], [0, 0, 6, 6, 0], [0, 1, 1, 4, 1], [0, 2, 3, 0, 0], [0, 3, 7, 3, 8], [0, 4, 2, 0, 7], [0, 5, 8, 7, 6], [0, 6, 5, 5, 5], [0, 7, 0, 2, 4], [0, 8, 4, 8, 3]],
  [[0, 0, 0, 1, 3], [0, 0, 1, 5, 2], [0, 1, 3, 3, 1], [0, 2, 2, 0, 8], [0, 3, 8, 7, 7], [0, 4, 7, 4, 0], [0, 5, 0, 2, 5], [0, 6, 4, 0, 4], [0, 7, 6, 6, 6], [0, 8, 5, 8, 0]],
  [[0, 0, 0, 1, 3], [0, 0, 6, 2, 2], [0, 1, 5, 5, 0], [0, 2, 2, 0, 8], [0, 3, 1, 3, 1], [0, 4, 3, 0, 5], [0, 5, 8, 8, 0], [0, 6, 7, 6, 6], [0, 7, 0, 4, 7], [0, 8, 4, 7, 4]],
  [[0, 0, 0, 1, 4], [0, 0, 1, 7, 0], [0, 1, 4, 0, 0], [0, 2, 6, 6, 3], [0, 3, 8, 3, 8], [0, 4, 2, 4, 2], [0, 5, 5, 8, 7], [0, 6, 3, 2, 6], [0, 7, 0, 0, 1], [0, 8, 7, 5, 5]],
  [[0, 0, 1, 1, 3], [0, 0, 4, 4, 7], [0, 1, 0, 3, 1], [0, 2, 8, 0, 8], [0, 3, 5, 0, 5], [0, 4, 0, 7, 4], [0, 5, 3, 5, 0], [0, 6, 6, 2, 2], [0, 7, 7, 6, 6], [0, 8, 2, 8, 0]],
  [[0, 0, 1, 1, 3], [0, 0, 5, 5, 2], [0, 1, 0, 3, 1], [0, 2, 8, 0, 8], [0, 3, 3, 7, 7], [0, 4, 6, 4, 0], [0, 5, 0, 2, 5], [0, 6, 4, 0, 4], [0, 7, 7, 6, 6], [0, 8, 2, 8, 0]]
]
structure LinearWitness where
  classIndex : Nat
  low : List Nat
  multiplier : List Nat
@[expose] def witnesses : List LinearWitness := [
  ⟨0, [2, 1, 1, 0, 0, 1, 0, 2, 0, 2], [2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 2, 1, 0]⟩,
  ⟨1, [1, 0, 0, 2, 0, 2, 2, 1, 0, 1], [2, 0, 1, 0, 0, 0, 2, 1, 0, 2, 1, 0, 0, 0, 0]⟩,
  ⟨1, [2, 0, 2, 0, 0, 1, 1, 1, 0, 2], [0, 0, 0, 2, 0, 2, 2, 1, 0, 2, 1, 0, 0, 0, 0]⟩,
  ⟨2, [0, 1, 0, 2, 2, 1, 0, 0, 2, 1], [0, 1, 2, 2, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨2, [0, 1, 2, 0, 2, 0, 1, 0, 1, 2], [1, 2, 0, 1, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨2, [0, 2, 0, 1, 1, 2, 0, 0, 1, 2], [1, 2, 0, 1, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨2, [0, 2, 1, 0, 1, 0, 2, 0, 2, 1], [0, 1, 2, 2, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨2, [1, 0, 1, 2, 2, 0, 1, 0, 2, 0], [2, 2, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]⟩,
  ⟨2, [1, 0, 2, 1, 2, 1, 0, 0, 0, 2], [2, 0, 2, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0]⟩,
  ⟨2, [1, 2, 0, 1, 0, 1, 2, 0, 2, 0], [2, 1, 0, 2, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0]⟩,
  ⟨2, [1, 2, 1, 0, 0, 2, 1, 0, 0, 2], [2, 2, 2, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0]⟩,
  ⟨2, [2, 0, 1, 2, 1, 2, 0, 0, 0, 1], [2, 1, 0, 2, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨2, [2, 0, 2, 1, 1, 0, 2, 0, 1, 0], [1, 0, 2, 0, 2, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨2, [2, 1, 0, 2, 0, 2, 1, 0, 1, 0], [0, 2, 1, 1, 0, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨2, [2, 1, 2, 0, 0, 1, 2, 0, 0, 1], [2, 1, 0, 2, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨3, [0, 1, 0, 1, 2, 2, 0, 0, 1, 2], [1, 2, 0, 1, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨3, [0, 1, 1, 0, 2, 0, 2, 0, 2, 1], [1, 2, 0, 1, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨3, [0, 2, 0, 2, 1, 1, 0, 0, 2, 1], [2, 0, 1, 0, 1, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨3, [0, 2, 2, 0, 1, 0, 1, 0, 1, 2], [1, 2, 0, 1, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨3, [1, 0, 0, 1, 2, 1, 2, 0, 2, 0], [2, 2, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]⟩,
  ⟨3, [1, 0, 1, 0, 2, 2, 1, 0, 0, 2], [0, 1, 0, 2, 2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]⟩,
  ⟨3, [1, 2, 1, 2, 0, 0, 1, 0, 2, 0], [2, 1, 0, 2, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0]⟩,
  ⟨3, [1, 2, 2, 1, 0, 1, 0, 0, 0, 2], [2, 2, 2, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0]⟩,
  ⟨3, [2, 0, 0, 2, 1, 2, 1, 0, 1, 0], [1, 0, 2, 0, 2, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨3, [2, 0, 2, 0, 1, 1, 2, 0, 0, 1], [2, 1, 0, 2, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨3, [2, 1, 1, 2, 0, 2, 0, 0, 0, 1], [2, 1, 0, 2, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨3, [2, 1, 2, 1, 0, 0, 2, 0, 1, 0], [1, 0, 2, 0, 2, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨4, [2, 1, 1, 0, 2, 1, 2, 0, 0, 0], [2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 2, 1, 0]⟩,
  ⟨5, [1, 0, 0, 2, 2, 0, 0, 1, 1, 2], [0, 2, 1, 0, 0, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0]⟩,
  ⟨5, [1, 0, 1, 2, 0, 2, 0, 2, 0, 1], [0, 2, 1, 1, 2, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0]⟩,
  ⟨5, [1, 1, 1, 2, 2, 0, 2, 0, 0, 0], [0, 2, 1, 0, 0, 0, 1, 2, 0, 2, 1, 0, 0, 0, 0]⟩,
  ⟨5, [1, 2, 0, 2, 0, 2, 1, 0, 1, 0], [2, 1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0]⟩,
  ⟨5, [2, 0, 1, 1, 2, 2, 0, 0, 1, 0], [0, 2, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0]⟩,
  ⟨6, [1, 0, 1, 0, 2, 0, 2, 2, 1, 0], [1, 2, 0, 1, 1, 1, 2, 1, 0, 0, 0, 0, 2, 1, 0]⟩,
  ⟨6, [1, 0, 1, 2, 0, 2, 0, 2, 0, 1], [0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0]⟩,
  ⟨6, [1, 2, 1, 0, 2, 1, 0, 0, 0, 2], [2, 0, 1, 0, 0, 0, 2, 1, 0, 2, 1, 0, 0, 0, 0]⟩,
  ⟨6, [1, 2, 1, 2, 0, 0, 1, 0, 2, 0], [2, 0, 1, 2, 1, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0]⟩,
  ⟨10, [0, 0, 2, 1, 0, 2, 1, 0, 2, 1], [2, 0, 2, 0, 0, 0, 2, 1, 0, 1, 2, 0, 1, 2, 0]⟩,
  ⟨10, [0, 1, 1, 2, 2, 0, 1, 0, 2, 0], [0, 1, 2, 2, 1, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0]⟩,
  ⟨10, [0, 1, 2, 1, 2, 1, 0, 0, 0, 2], [2, 1, 0, 0, 1, 2, 1, 0, 2, 0, 0, 0, 0, 0, 0]⟩,
  ⟨10, [0, 2, 1, 1, 1, 2, 2, 0, 0, 0], [2, 2, 2, 2, 1, 0, 2, 1, 0, 0, 1, 0, 0, 0, 0]⟩,
  ⟨10, [1, 0, 2, 2, 2, 0, 0, 0, 1, 1], [0, 2, 1, 1, 2, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0]⟩,
  ⟨10, [1, 1, 0, 2, 1, 0, 2, 0, 0, 2], [0, 2, 0, 2, 0, 2, 1, 1, 1, 0, 0, 0, 0, 0, 0]⟩,
  ⟨10, [1, 2, 0, 2, 0, 2, 1, 0, 1, 0], [2, 0, 1, 0, 0, 0, 0, 2, 0, 1, 2, 0, 0, 0, 0]⟩,
  ⟨10, [1, 2, 2, 0, 0, 1, 2, 0, 0, 1], [0, 1, 0, 1, 1, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0]⟩,
  ⟨10, [2, 0, 0, 1, 1, 2, 0, 0, 1, 2], [2, 0, 1, 0, 0, 0, 0, 2, 0, 1, 2, 0, 0, 0, 0]⟩,
  ⟨10, [2, 0, 1, 0, 1, 0, 2, 0, 2, 1], [0, 0, 0, 1, 0, 2, 0, 1, 0, 2, 1, 0, 0, 0, 0]⟩,
  ⟨10, [2, 1, 0, 0, 0, 1, 1, 0, 2, 2], [2, 0, 1, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0]⟩,
  ⟨10, [2, 2, 1, 0, 2, 1, 0, 0, 1, 0], [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨11, [0, 0, 0, 1, 1, 1, 0, 2, 2, 2], [1, 0, 2, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨11, [0, 0, 1, 1, 2, 0, 2, 1, 2, 0], [0, 0, 2, 0, 0, 2, 0, 0, 0, 1, 1, 0, 2, 0, 0]⟩,
  ⟨11, [0, 0, 2, 0, 2, 1, 1, 1, 0, 2], [0, 0, 2, 0, 0, 2, 0, 0, 0, 1, 1, 0, 2, 0, 0]⟩,
  ⟨11, [0, 0, 2, 2, 1, 0, 1, 2, 1, 0], [2, 0, 1, 2, 1, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨11, [1, 0, 0, 0, 2, 1, 2, 0, 2, 1], [0, 1, 2, 2, 2, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0]⟩,
  ⟨11, [1, 0, 0, 1, 0, 2, 2, 2, 1, 0], [0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨11, [1, 0, 1, 2, 2, 2, 1, 0, 0, 0], [1, 1, 2, 1, 2, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0]⟩,
  ⟨11, [1, 0, 2, 2, 0, 1, 0, 2, 0, 1], [0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨11, [2, 0, 0, 0, 1, 2, 1, 0, 1, 2], [0, 0, 0, 1, 1, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨11, [2, 0, 1, 1, 0, 2, 0, 1, 0, 2], [0, 0, 2, 0, 0, 2, 1, 1, 0, 0, 0, 0, 2, 0, 0]⟩,
  ⟨11, [2, 0, 1, 2, 1, 0, 0, 0, 2, 1], [1, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨11, [2, 0, 2, 0, 0, 0, 2, 1, 1, 1], [2, 2, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 2, 0, 0]⟩,
  ⟨12, [0, 1, 1, 0, 2, 2, 2, 0, 0, 1], [2, 1, 0, 1, 1, 1, 1, 2, 0, 0, 0, 0, 2, 1, 0]⟩,
  ⟨12, [0, 2, 0, 2, 1, 2, 0, 0, 1, 1], [0, 0, 0, 0, 2, 1, 2, 1, 0, 0, 0, 0, 1, 2, 0]⟩,
  ⟨12, [1, 0, 0, 2, 0, 2, 2, 1, 0, 1], [2, 0, 1, 0, 0, 0, 2, 1, 0, 2, 1, 0, 0, 0, 0]⟩,
  ⟨13, [0, 2, 2, 0, 1, 1, 1, 0, 0, 2], [0, 2, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0]⟩,
  ⟨14, [0, 0, 0, 1, 1, 2, 2, 1, 0, 2], [0, 0, 2, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0]⟩,
  ⟨14, [0, 1, 0, 1, 2, 1, 0, 0, 2, 2], [0, 2, 1, 1, 2, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0]⟩,
  ⟨14, [0, 2, 0, 0, 2, 1, 2, 1, 1, 0], [1, 0, 2, 2, 2, 2, 0, 0, 0, 1, 2, 0, 2, 1, 0]⟩,
  ⟨14, [1, 0, 2, 1, 2, 1, 2, 0, 0, 0], [1, 0, 2, 0, 1, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0]⟩,
  ⟨14, [2, 0, 1, 0, 2, 1, 0, 1, 0, 2], [0, 2, 1, 0, 0, 0, 2, 1, 0, 1, 2, 0, 0, 0, 0]⟩,
  ⟨15, [1, 0, 1, 0, 2, 0, 2, 2, 1, 0], [2, 0, 0, 1, 2, 2, 2, 0, 0, 2, 0, 0, 2, 0, 0]⟩
]
@[expose] def total (xs : List Nat) : Nat := xs.foldl Nat.add 0

@[expose] def entry (classIndex row column : Nat) : Nat :=
  ((representatives.getD classIndex []).getD row []).getD column 0

@[expose] def phaseAt (w : LinearWitness) (row column : Nat) : Nat :=
  (w.low.getD row 0 + 3 - entry w.classIndex row column % 3) % 3

@[expose] def coefficient (w : LinearWitness) (equation row : Nat) : Nat :=
  if phaseAt w row (equation / 3) = equation % 3 then 1 else 0

@[expose] def rhs (w : LinearWitness) (equation : Nat) : Nat :=
  total ((List.range 10).map (fun row =>
    coefficient w equation row *
      (entry w.classIndex row (equation / 3) / 3 +
        if w.low.getD row 0 < entry w.classIndex row (equation / 3) % 3 then 1 else 0))) % 3

end CoveringFormalRound3Linear


-- CertifiedLinear
namespace CoveringCertifiedLinear
open CoveringF3 CoveringFormalRound3Linear
@[expose] def matrix3 (w : LinearWitness) (r c : Nat) : F3 := ofNat (coefficient w r c)
@[expose] def right3 (w : LinearWitness) (r : Nat) : F3 := ofNat (rhs w r)
@[expose] def multiplier3 (w : LinearWitness) (r : Nat) : F3 := ofNat (w.multiplier.getD r 0)

@[expose] def ValidCertificate (w : LinearWitness) : Prop :=
  (∀ c : Fin 10, CoveringF3.sum 15 (fun r => mul (multiplier3 w r) (matrix3 w r c.val)) = 0) ∧
  CoveringF3.sum 15 (fun r => mul (multiplier3 w r) (right3 w r)) = 1

instance (w : LinearWitness) : Decidable (ValidCertificate w) := by
  unfold ValidCertificate
  infer_instance
@[expose] def validCertificate (w : LinearWitness) : Bool := decide (ValidCertificate w)

theorem allCertificatesValid : witnesses.all validCertificate = true := by decide

theorem valid_of_member (w : LinearWitness) (h : w ∈ witnesses) : ValidCertificate w := by
  have hh := List.all_eq_true.mp allCertificatesValid w h
  exact of_decide_eq_true hh
theorem no_linear_solution (w : LinearWitness) (h : w ∈ witnesses) :
    ¬ ∃ v : Nat → F3, ∀ r, r < 15 →
      CoveringF3.sum 10 (fun c => mul (matrix3 w r c) (v c)) = right3 w r := by
  obtain ⟨hA, hb⟩ := valid_of_member w h
  exact left_nullspace_sound 15 10 (matrix3 w) (right3 w) (multiplier3 w)
    (fun c hc => hA ⟨c,hc⟩) hb
end CoveringCertifiedLinear


-- ExceptionalProfile
namespace CoveringExceptional
open CoveringF3 CoveringFormalRound3Linear
@[expose] def exceptional : LinearWitness := ⟨12, [1, 1, 0, 2, 2, 0, 2, 0, 1, 0], []⟩
@[expose] def matrix3 (r c : Nat) : F3 := ofNat (coefficient exceptional r c)
@[expose] def right3 (r : Nat) : F3 := ofNat (rhs exceptional r)
@[expose] def particular : List Nat := [1, 2, 2, 1, 1, 1, 1, 0, 0, 0]
@[expose] def direction : List Nat := [1, 1, 2, 2, 1, 0, 0, 0, 1, 1]
@[expose] def leftMultipliers : List (List Nat) := [
  [0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  [0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
  [0, 1, 0, 1, 0, 0, 2, 0, 0, 2, 1, 0, 0, 0, 0],
  [0, 2, 0, 2, 2, 0, 2, 1, 0, 1, 1, 0, 0, 0, 0],
  [0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  [1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0],
  [0, 2, 1, 1, 0, 0, 1, 2, 0, 2, 1, 0, 0, 0, 0],
  [0, 1, 2, 1, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  [0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]
@[expose] def point (c : Nat) : F3 := ofNat (particular.getD c 0)
@[expose] def dir (c : Nat) : F3 := ofNat (direction.getD c 0)
@[expose] def multiplier (j r : Nat) : F3 := ofNat ((leftMultipliers.getD j []).getD r 0)

theorem inverse_minor_certificate : ∀ j : Fin 9,
    (∀ c : Fin 10, CoveringF3.sum 15 (fun r => mul (multiplier j.val r) (matrix3 r c.val)) =
      affineRow j.val 9 (dir j.val) c.val) ∧
    CoveringF3.sum 15 (fun r => mul (multiplier j.val r) (right3 r)) = point j.val := by decide

theorem affine_line (v : Nat → F3)
    (hv : ∀ r, r < 15 → CoveringF3.sum 10 (fun c => mul (matrix3 r c) (v c)) = right3 r) :
    ∀ j, j < 10 → v j = add (point j) (mul (dir j) (v 9)) := by
  intro j hj
  by_cases hfree : j = 9
  · subst j
    simp only [point, dir, particular, direction, List.getD]
    change v 9 = add 0 (mul 1 (v 9))
    rw [mul_one, zero_add]
  · have hj9 : j < 9 := by omega
    obtain ⟨hA, hb⟩ := inverse_minor_certificate ⟨j,hj9⟩
    have hc := certified_consequence 15 10 matrix3 right3 (multiplier j)
      (affineRow j 9 (dir j)) v (point j) (fun c hc => hA ⟨c,hc⟩) hb hv
    rw [sum_affine_row 10 j 9 hj (by decide)] at hc
    exact recover_affine (v j) (point j) (dir j) (v 9) hc
@[expose] def upperDifference (v : Nat → F3) (r j : Nat) : F3 :=
  add (v r) (neg (ofNat (entry 12 r j / 3 +
    if exceptional.low.getD r 0 < entry 12 r j % 3 then 1 else 0)))

@[expose] def quadratic (v : Nat → F3) : F3 :=
  add (mul (upperDifference v 0 2) (upperDifference v 0 2))
    (add (mul (upperDifference v 8 2) (upperDifference v 8 2))
      (mul (upperDifference v 9 2) (upperDifference v 9 2)))

theorem quadratic_failure_in_original_fibre : ∀ t : F3,
    quadratic (fun c => add (point c) (mul (dir c) t)) ≠ 2 := by decide

theorem no_fibre_solution (v : Nat → F3)
    (hv : ∀ r, r < 15 → CoveringF3.sum 10 (fun c => mul (matrix3 r c) (v c)) = right3 r)
    (hq : quadratic v = 2) : False := by
  have ha := affine_line v hv
  have h0 := ha 0 (by decide)
  have h8 := ha 8 (by decide)
  have h9 := ha 9 (by decide)
  apply quadratic_failure_in_original_fibre (v 9)
  have heq : quadratic v = quadratic (fun c => add (point c) (mul (dir c) (v 9))) := by
    unfold quadratic upperDifference
    rw [h0, h8]
    simp only [show point 9 = 0 by decide, show dir 9 = 1 by decide, mul_one, zero_add]
  exact heq.symm.trans hq
end CoveringExceptional


-- ProfileEnumeration
namespace CoveringProfiles
abbrev Trit := Fin 3
@[expose] def count (d : Trit) : List Trit → Nat
  | [] => 0
  | a :: xs => (if a = d then 1 else 0) + count d xs
@[expose] def quotaWords : Nat → Nat → Nat → Nat → List (List Trit)
  | 0, z, o, t => if z = 0 ∧ o = 0 ∧ t = 0 then [[]] else []
  | n+1, z, o, t =>
    (if z > 0 then (quotaWords n (z-1) o t).map (0 :: ·) else []) ++
    (if o > 0 then (quotaWords n z (o-1) t).map (1 :: ·) else []) ++
    (if t > 0 then (quotaWords n z o (t-1)).map (2 :: ·) else [])

theorem trit_cases : ∀ a : Trit, a = 0 ∨ a = 1 ∨ a = 2 := by decide

theorem quota_complete (xs : List Trit) :
    xs ∈ quotaWords xs.length (count 0 xs) (count 1 xs) (count 2 xs) := by
  induction xs with
  | nil => decide
  | cons a xs ih =>
    rcases trit_cases a with rfl | rfl | rfl
    all_goals simp [quotaWords, count, Nat.add_sub_cancel_left, ih, List.mem_map]
    all_goals omega
@[expose] def balancedWords : List (List Trit) := quotaWords 10 4 3 3

theorem balanced_complete (xs : List Trit)
    (hlen : xs.length = 10) (hz : count 0 xs = 4)
    (ho : count 1 xs = 3) (ht : count 2 xs = 3) : xs ∈ balancedWords := by
  simpa [balancedWords, hlen, hz, ho, ht] using quota_complete xs

end CoveringProfiles


-- ProfileData
namespace CoveringProfileData
open CoveringProfiles CoveringFormalRound3Linear
@[expose] def lowerColumns : List (List (List Trit)) := [
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 1, 2, 0, 1, 2], [0, 1, 0, 2, 1, 1, 2, 2, 0, 0], [1, 0, 1, 2, 0, 2, 1, 2, 0, 0], [1, 1, 0, 1, 0, 2, 2, 0, 0, 2]],
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 1, 2, 0, 1, 2], [0, 1, 0, 2, 2, 1, 0, 1, 0, 2], [1, 2, 0, 0, 1, 1, 2, 0, 0, 2], [1, 0, 0, 1, 0, 1, 0, 2, 2, 2]],
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 1, 2, 0, 1, 2], [0, 0, 2, 1, 0, 2, 1, 0, 2, 1], [1, 0, 0, 0, 2, 2, 2, 0, 1, 1], [1, 2, 2, 2, 0, 0, 0, 0, 1, 1]],
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 1, 2, 0, 1, 2], [0, 0, 2, 1, 0, 2, 1, 0, 2, 1], [1, 0, 2, 2, 2, 0, 0, 0, 1, 1], [1, 2, 0, 0, 0, 2, 2, 0, 1, 1]],
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 1, 2, 0, 1, 2], [0, 1, 1, 2, 2, 0, 0, 1, 0, 2], [1, 0, 2, 2, 2, 1, 0, 0, 0, 1], [1, 1, 2, 1, 0, 0, 2, 0, 0, 2]],
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 1, 2, 0, 1, 2], [0, 2, 1, 2, 1, 0, 0, 2, 1, 0], [1, 0, 2, 1, 0, 0, 2, 2, 1, 0], [1, 2, 1, 1, 0, 0, 0, 0, 2, 2]],
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 1, 2, 0, 1, 2], [0, 0, 1, 0, 2, 2, 1, 0, 2, 1], [1, 2, 0, 0, 0, 2, 2, 0, 1, 1], [1, 0, 0, 0, 0, 1, 1, 2, 2, 2]],
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 1, 2, 0, 1, 2], [0, 2, 1, 2, 1, 0, 2, 1, 0, 0], [1, 2, 0, 0, 1, 1, 2, 0, 0, 2], [1, 2, 0, 2, 0, 0, 0, 1, 1, 2]],
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 1, 2, 0, 1, 2], [0, 2, 1, 2, 1, 0, 2, 1, 0, 0], [1, 2, 0, 0, 1, 1, 2, 0, 0, 2], [1, 2, 0, 2, 0, 0, 0, 1, 1, 2]],
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 1, 2, 0, 1, 2], [0, 2, 1, 2, 1, 0, 2, 1, 0, 0], [1, 2, 0, 0, 1, 1, 2, 0, 0, 2], [1, 2, 0, 2, 0, 0, 0, 1, 1, 2]],
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 1, 2, 0, 1, 2], [0, 1, 0, 0, 2, 2, 2, 0, 1, 1], [1, 0, 0, 1, 2, 1, 2, 0, 2, 0], [2, 1, 2, 1, 0, 0, 2, 0, 1, 0]],
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 1, 2, 0, 1, 2], [0, 0, 1, 0, 1, 2, 2, 2, 0, 1], [1, 0, 1, 0, 0, 0, 1, 2, 2, 2], [2, 0, 1, 0, 2, 1, 0, 2, 1, 0]],
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 1, 2, 0, 1, 2], [0, 1, 0, 2, 2, 1, 0, 1, 0, 2], [1, 2, 0, 0, 1, 1, 2, 0, 0, 2], [0, 2, 1, 2, 1, 0, 2, 1, 0, 0]],
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 1, 2, 0, 1, 2], [0, 0, 2, 2, 1, 0, 2, 1, 0, 1], [1, 2, 2, 0, 0, 0, 2, 0, 1, 1], [0, 2, 0, 2, 1, 2, 0, 0, 1, 1]],
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 1, 2, 0, 1, 2], [0, 1, 1, 0, 2, 2, 2, 0, 0, 1], [1, 1, 0, 0, 0, 1, 2, 2, 0, 2], [1, 0, 0, 0, 2, 2, 1, 0, 1, 2]],
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 1, 2, 0, 1, 2], [1, 1, 0, 2, 2, 0, 0, 0, 1, 2], [1, 1, 0, 0, 0, 1, 2, 2, 0, 2], [0, 1, 1, 2, 2, 1, 0, 2, 0, 0]],
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 2, 0, 1, 2, 0, 1, 2], [1, 2, 0, 2, 0, 0, 0, 1, 1, 2], [1, 2, 0, 0, 1, 1, 2, 0, 0, 2], [0, 2, 1, 2, 1, 0, 2, 1, 0, 0]]
]
@[expose] def expectedProfiles : List (List (List Trit)) := [
  [[2, 1, 1, 0, 0, 1, 0, 2, 0, 2]],
  [[1, 0, 0, 2, 0, 2, 2, 1, 0, 1], [2, 0, 2, 0, 0, 1, 1, 1, 0, 2]],
  [[0, 1, 0, 2, 2, 1, 0, 0, 2, 1], [0, 1, 2, 0, 2, 0, 1, 0, 1, 2], [0, 2, 0, 1, 1, 2, 0, 0, 1, 2], [0, 2, 1, 0, 1, 0, 2, 0, 2, 1], [1, 0, 1, 2, 2, 0, 1, 0, 2, 0], [1, 0, 2, 1, 2, 1, 0, 0, 0, 2], [1, 2, 0, 1, 0, 1, 2, 0, 2, 0], [1, 2, 1, 0, 0, 2, 1, 0, 0, 2], [2, 0, 1, 2, 1, 2, 0, 0, 0, 1], [2, 0, 2, 1, 1, 0, 2, 0, 1, 0], [2, 1, 0, 2, 0, 2, 1, 0, 1, 0], [2, 1, 2, 0, 0, 1, 2, 0, 0, 1]],
  [[0, 1, 0, 1, 2, 2, 0, 0, 1, 2], [0, 1, 1, 0, 2, 0, 2, 0, 2, 1], [0, 2, 0, 2, 1, 1, 0, 0, 2, 1], [0, 2, 2, 0, 1, 0, 1, 0, 1, 2], [1, 0, 0, 1, 2, 1, 2, 0, 2, 0], [1, 0, 1, 0, 2, 2, 1, 0, 0, 2], [1, 2, 1, 2, 0, 0, 1, 0, 2, 0], [1, 2, 2, 1, 0, 1, 0, 0, 0, 2], [2, 0, 0, 2, 1, 2, 1, 0, 1, 0], [2, 0, 2, 0, 1, 1, 2, 0, 0, 1], [2, 1, 1, 2, 0, 2, 0, 0, 0, 1], [2, 1, 2, 1, 0, 0, 2, 0, 1, 0]],
  [[2, 1, 1, 0, 2, 1, 2, 0, 0, 0]],
  [[1, 0, 0, 2, 2, 0, 0, 1, 1, 2], [1, 0, 1, 2, 0, 2, 0, 2, 0, 1], [1, 1, 1, 2, 2, 0, 2, 0, 0, 0], [1, 2, 0, 2, 0, 2, 1, 0, 1, 0], [2, 0, 1, 1, 2, 2, 0, 0, 1, 0]],
  [[1, 0, 1, 0, 2, 0, 2, 2, 1, 0], [1, 0, 1, 2, 0, 2, 0, 2, 0, 1], [1, 2, 1, 0, 2, 1, 0, 0, 0, 2], [1, 2, 1, 2, 0, 0, 1, 0, 2, 0]],
  [],
  [],
  [],
  [[0, 0, 2, 1, 0, 2, 1, 0, 2, 1], [0, 1, 1, 2, 2, 0, 1, 0, 2, 0], [0, 1, 2, 1, 2, 1, 0, 0, 0, 2], [0, 2, 1, 1, 1, 2, 2, 0, 0, 0], [1, 0, 2, 2, 2, 0, 0, 0, 1, 1], [1, 1, 0, 2, 1, 0, 2, 0, 0, 2], [1, 2, 0, 2, 0, 2, 1, 0, 1, 0], [1, 2, 2, 0, 0, 1, 2, 0, 0, 1], [2, 0, 0, 1, 1, 2, 0, 0, 1, 2], [2, 0, 1, 0, 1, 0, 2, 0, 2, 1], [2, 1, 0, 0, 0, 1, 1, 0, 2, 2], [2, 2, 1, 0, 2, 1, 0, 0, 1, 0]],
  [[0, 0, 0, 1, 1, 1, 0, 2, 2, 2], [0, 0, 1, 1, 2, 0, 2, 1, 2, 0], [0, 0, 2, 0, 2, 1, 1, 1, 0, 2], [0, 0, 2, 2, 1, 0, 1, 2, 1, 0], [1, 0, 0, 0, 2, 1, 2, 0, 2, 1], [1, 0, 0, 1, 0, 2, 2, 2, 1, 0], [1, 0, 1, 2, 2, 2, 1, 0, 0, 0], [1, 0, 2, 2, 0, 1, 0, 2, 0, 1], [2, 0, 0, 0, 1, 2, 1, 0, 1, 2], [2, 0, 1, 1, 0, 2, 0, 1, 0, 2], [2, 0, 1, 2, 1, 0, 0, 0, 2, 1], [2, 0, 2, 0, 0, 0, 2, 1, 1, 1]],
  [[0, 1, 1, 0, 2, 2, 2, 0, 0, 1], [0, 2, 0, 2, 1, 2, 0, 0, 1, 1], [1, 0, 0, 2, 0, 2, 2, 1, 0, 1], [1, 1, 0, 2, 2, 0, 2, 0, 1, 0]],
  [[0, 2, 2, 0, 1, 1, 1, 0, 0, 2]],
  [[0, 0, 0, 1, 1, 2, 2, 1, 0, 2], [0, 1, 0, 1, 2, 1, 0, 0, 2, 2], [0, 2, 0, 0, 2, 1, 2, 1, 1, 0], [1, 0, 2, 1, 2, 1, 2, 0, 0, 0], [2, 0, 1, 0, 2, 1, 0, 1, 0, 2]],
  [[1, 0, 1, 0, 2, 0, 2, 2, 1, 0]],
  []
]
@[expose] def histogram : List Nat → Nat × Nat × Nat
  | [] => (0,0,0)
  | x :: xs =>
    let h := histogram xs
    if x = 0 then (h.1+1,h.2.1,h.2.2)
    else if x = 1 then (h.1,h.2.1+1,h.2.2)
    else if x = 2 then (h.1,h.2.1,h.2.2+1)
    else h
@[expose] def columnOK (xs col : List Trit) : Bool :=
  decide (histogram (List.zipWith (fun a b : Trit => (a.val+3-b.val)%3) xs col) = (4,3,3))

@[expose] def profileOK (c : Nat) (xs : List Trit) : Bool :=
  ((lowerColumns.getD c []).drop 1).all (columnOK xs)
@[expose] def filteredProfiles (c : Nat) : List (List Trit) := balancedWords.filter (profileOK c)

end CoveringProfileData


-- Finite profile tables (seventeen separately checked propositions).
namespace CoveringProfileChecks
open CoveringProfileData
theorem profile00 : filteredProfiles 0 = expectedProfiles.getD 0 [] := by decide
theorem profile01 : filteredProfiles 1 = expectedProfiles.getD 1 [] := by decide
theorem profile02 : filteredProfiles 2 = expectedProfiles.getD 2 [] := by decide
theorem profile03 : filteredProfiles 3 = expectedProfiles.getD 3 [] := by decide
theorem profile04 : filteredProfiles 4 = expectedProfiles.getD 4 [] := by decide
theorem profile05 : filteredProfiles 5 = expectedProfiles.getD 5 [] := by decide
theorem profile06 : filteredProfiles 6 = expectedProfiles.getD 6 [] := by decide
theorem profile07 : filteredProfiles 7 = expectedProfiles.getD 7 [] := by decide
theorem profile08 : filteredProfiles 8 = expectedProfiles.getD 8 [] := by decide
theorem profile09 : filteredProfiles 9 = expectedProfiles.getD 9 [] := by decide
theorem profile10 : filteredProfiles 10 = expectedProfiles.getD 10 [] := by decide
theorem profile11 : filteredProfiles 11 = expectedProfiles.getD 11 [] := by decide
theorem profile12 : filteredProfiles 12 = expectedProfiles.getD 12 [] := by decide
theorem profile13 : filteredProfiles 13 = expectedProfiles.getD 13 [] := by decide
theorem profile14 : filteredProfiles 14 = expectedProfiles.getD 14 [] := by decide
theorem profile15 : filteredProfiles 15 = expectedProfiles.getD 15 [] := by decide
theorem profile16 : filteredProfiles 16 = expectedProfiles.getD 16 [] := by decide
end CoveringProfileChecks

-- ProfileCoverage
namespace CoveringProfileCoverage
open CoveringProfiles CoveringProfileData CoveringProfileChecks CoveringFormalRound3Linear

theorem profile_tables (c : Nat) (hc : c < 17) :
    filteredProfiles c = expectedProfiles.getD c [] := by
  have h : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨
      c = 8 ∨ c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 ∨ c = 16 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile00
  · exact profile01
  · exact profile02
  · exact profile03
  · exact profile04
  · exact profile05
  · exact profile06
  · exact profile07
  · exact profile08
  · exact profile09
  · exact profile10
  · exact profile11
  · exact profile12
  · exact profile13
  · exact profile14
  · exact profile15
  · exact profile16
@[expose] def Eligible (c : Nat) (xs : List Trit) : Prop :=
  xs.length = 10 ∧ count 0 xs = 4 ∧ count 1 xs = 3 ∧ count 2 xs = 3 ∧ profileOK c xs = true

theorem every_eligible_profile_is_listed (c : Nat) (hc : c < 17)
    (xs : List Trit) (h : Eligible c xs) : xs ∈ expectedProfiles.getD c [] := by
  obtain ⟨hlen,hz,ho,ht,hcols⟩ := h
  rw [← profile_tables c hc]
  exact List.mem_filter.mpr ⟨balanced_complete xs hlen hz ho ht, hcols⟩

@[expose] def hasCertificate (c : Nat) (xs : List Trit) : Bool :=
  witnesses.any (fun w => decide (w.classIndex = c ∧ w.low = xs.map Fin.val)) ||
  decide (c = 12 ∧ xs.map Fin.val = CoveringExceptional.exceptional.low)

theorem all_profiles_have_certificates : ∀ c : Fin 17,
    (expectedProfiles.getD c.val []).all (hasCertificate c.val) = true := by decide

theorem every_eligible_profile_has_certificate (c : Nat) (hc : c < 17)
    (xs : List Trit) (h : Eligible c xs) :
    (∃ w ∈ witnesses, w.classIndex = c ∧ w.low = xs.map Fin.val) ∨
    (c = 12 ∧ xs.map Fin.val = CoveringExceptional.exceptional.low) := by
  have hmem := every_eligible_profile_is_listed c hc xs h
  have hh := List.all_eq_true.mp (all_profiles_have_certificates ⟨c,hc⟩) xs hmem
  obtain hl | hr := Bool.or_eq_true_iff.mp hh
  · obtain ⟨w,hw,hmatch⟩ := List.any_eq_true.mp hl
    exact Or.inl ⟨w,hw,of_decide_eq_true hmatch⟩
  · exact Or.inr (of_decide_eq_true hr)
end CoveringProfileCoverage


-- ArithmeticExclusion
namespace CoveringArithmeticExclusion
open CoveringF3 CoveringProfiles CoveringFormalRound3Linear CoveringProfileCoverage

@[expose] def base (c : Nat) (xs : List Trit) : LinearWitness := ⟨c,xs.map Fin.val,[]⟩
@[expose] def upper (w : LinearWitness) (v : Nat → F3) (r j : Nat) : F3 :=
  add (v r) (neg (ofNat (entry w.classIndex r j / 3 +
    if w.low.getD r 0 < entry w.classIndex r j % 3 then 1 else 0)))
@[expose] def secondMoment (w : LinearWitness) (v : Nat → F3) (j t : Nat) : F3 :=
  CoveringF3.sum 10 (fun r => if phaseAt w r j = t then mul (upper w v r j) (upper w v r j) else 0)

@[expose] def LiftEquations (c : Nat) (xs : List Trit) (v : Nat → F3) : Prop :=
  (∀ r, r < 15 → CoveringF3.sum 10 (fun i =>
      mul (CoveringCertifiedLinear.matrix3 (base c xs) r i) (v i)) =
      CoveringCertifiedLinear.right3 (base c xs) r) ∧
  (∀ j, j < 5 → ∀ t, t < 3 → secondMoment (base c xs) v j t = 2)

theorem exceptional_moment_is_quadratic (v : Nat → F3) :
    secondMoment CoveringExceptional.exceptional v 2 1 = CoveringExceptional.quadratic v := by
  simp [secondMoment, CoveringF3.sum, phaseAt, CoveringExceptional.exceptional,
    entry, representatives, upper, CoveringExceptional.quadratic,
    CoveringExceptional.upperDifference, add_zero, zero_add, add_assoc]

theorem no_digit_lift (c : Nat) (hc : c < 17) (xs : List Trit)
    (he : Eligible c xs) : ¬ ∃ v : Nat → F3, LiftEquations c xs v := by
  rintro ⟨v,hl,hq⟩
  rcases every_eligible_profile_has_certificate c hc xs he with
    ⟨w,hw,hci,hlo⟩ | ⟨hci,hlo⟩
  · apply CoveringCertifiedLinear.no_linear_solution w hw
    refine ⟨v,?_⟩
    simpa [CoveringCertifiedLinear.matrix3, CoveringCertifiedLinear.right3,
      base, coefficient, phaseAt, rhs, hci, hlo] using hl
  · subst c
    have hb : base 12 xs = CoveringExceptional.exceptional := by
      simp only [base, hlo]
      rfl
    rw [hb] at hl hq
    apply CoveringExceptional.no_fibre_solution v
    · exact hl
    · rw [← exceptional_moment_is_quadratic]
      exact hq 2 (by decide) 1 (by decide)
end CoveringArithmeticExclusion


-- RepresentativeExtension
namespace CyclicRepresentativeExtension
open CyclicNormalization CoveringFormalRound3Linear
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
end CyclicRepresentativeExtension


-- RepresentativeEligibility
namespace CyclicRepresentativeExtension
open CyclicNormalization CoveringProfiles CoveringProfileData CoveringProfileCoverage

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
end CyclicRepresentativeExtension


-- DigitTransport
namespace CyclicDigitTransport
open CyclicNormalization CyclicRepresentativeExtension CoveringF3 CoveringProfiles
open CoveringFormalRound3Linear CoveringArithmeticExclusion
@[expose] def profile (z : Fin 10 → Fin 9) : List Trit := rows.map (fun r => low (z r))
@[expose] def vector (z : Fin 10 → Fin 9) (r : Nat) : F3 := if h : r < 10 then high (z ⟨r,h⟩) else 0

theorem profile_get (z : Fin 10 → Fin 9) (r : Fin 10) :
    ((profile z).map Fin.val).getD r.val 0 = (z r).val % 3 := by
  have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 := by omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem phase_eq (c : Fin 17) (z : Fin 10 → Fin 9) (r : Fin 10) (j : Fin 5) :
    phaseAt (base c.val (profile z)) r.val j.val =
    (low (translate (representative c r j) (z r))).val := by
  have hi : ∀ a b : Fin 9, (a.val % 3 + 3 - b.val % 3) % 3 =
      (low (translate b a)).val := by decide
  simpa only [phaseAt, base, profile_get, representative] using hi (z r) (representative c r j)

theorem upper_eq (c : Fin 17) (z : Fin 10 → Fin 9) (r : Fin 10) (j : Fin 5) :
    upper (base c.val (profile z)) (vector z) r.val j.val =
    high (translate (representative c r j) (z r)) := by
  have hi : ∀ a b : Fin 9,
      add (high a) (neg (ofNat (b.val / 3 + if a.val % 3 < b.val % 3 then 1 else 0))) =
      high (translate b a) := by decide
  have hv : vector z r.val = high (z r) := by
    simp only [vector, dite_eq_left r.isLt]
  simp only [upper, base, profile_get, hv]
  exact hi (z r) (representative c r j)
theorem ofNat_add (a b : Nat) : ofNat (a+b) = add (ofNat a) (ofNat b) := by
  apply Fin.ext
  simp [ofNat, add, Nat.add_mod]
theorem nat_sum_append (a b : List Nat) : (a++b).sum = a.sum+b.sum := by
  induction a with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_assoc]
theorem sum_ofNat (n : Nat) (f : Nat → Nat) :
    sum n (fun i => ofNat (f i)) = ofNat (((List.range n).map f).sum) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sum, ih, List.range_succ, nat_sum_append, ofNat_add]

theorem ofNat_total (xs : List Nat) : ofNat (total xs) = ofNat xs.sum := by
  have h : ∀ (l : List Nat) (a : Nat), l.foldl Nat.add a = a + l.sum := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons x xs ih => intro a; simp [ih, Nat.add_assoc]
  simp [total, h]
theorem sum10_rows (f : Fin 10 → Nat) :
    sum 10 (fun r => if h : r < 10 then ofNat (f ⟨r,h⟩) else 0) =
    ofNat (rows.map f).sum := by
  simp [rows, sum, ofNat_add, add_assoc, zero_add, add_zero]

@[expose] def momentTerm (square : Bool) (a : F3) : F3 := if square then mul a a else a

theorem momentTerm_nat (square : Bool) (a : Fin 9) :
    momentTerm square (high a) = ofNat (if square then (a.val / 3)*(a.val / 3) else a.val / 3) := by
  have h : ∀ square : Bool, ∀ a : Fin 9,
      momentTerm square (high a) = ofNat (if square then (a.val / 3)*(a.val / 3) else a.val / 3) := by decide
  exact h square a
theorem moments_transport (c : Fin 17) (z : Fin 10 → Fin 9)
    (hp : ∀ j : Fin 5, (rows.map (fun r => translate (representative c r j) (z r))).Perm (residues ++ [0]))
    (j : Fin 5) (t : Fin 3) (square : Bool) :
    sum 10 (fun r => if phaseAt (base c.val (profile z)) r j.val = t.val
      then momentTerm square (upper (base c.val (profile z)) (vector z) r j.val) else 0) =
      (if square then 2 else 0) := by
  let f : Fin 10 → Nat := fun r =>
    if low (translate (representative c r j) (z r)) = t then
      (if square then ((translate (representative c r j) (z r)).val / 3)*((translate (representative c r j) (z r)).val / 3)
      else (translate (representative c r j) (z r)).val / 3) else 0
  have he : sum 10 (fun r => if phaseAt (base c.val (profile z)) r j.val = t.val
      then momentTerm square (upper (base c.val (profile z)) (vector z) r j.val) else 0) = ofNat (rows.map f).sum := by
    rw [← sum10_rows f]
    apply sum_congr
    intro r hr
    rw [dif_pos hr, phase_eq c z ⟨r,hr⟩ j, upper_eq c z ⟨r,hr⟩ j, momentTerm_nat]
    have hh : (low (translate (representative c ⟨r,hr⟩ j) (z ⟨r,hr⟩))).val = t.val ↔
        low (translate (representative c ⟨r,hr⟩ j) (z ⟨r,hr⟩)) = t := Fin.val_inj
    simp only [hh, f]
    split <;> rfl
  rw [he]
  obtain ⟨h1,h2⟩ := normalized_conditional_moments (hp j) t
  apply Fin.ext
  cases square <;> simpa [ofNat, f, List.map_map, Function.comp_def] using (by assumption)

@[expose] def offset (w : LinearWitness) (r j : Nat) : Nat :=
    entry w.classIndex r j / 3 + if w.low.getD r 0 < entry w.classIndex r j % 3 then 1 else 0

theorem add_neg_cancel : ∀ a b : F3, add (add a (neg b)) b = a := by decide

theorem linear_point (w : LinearWitness) (v : Nat → F3) (e r : Nat) :
    mul (CoveringCertifiedLinear.matrix3 w e r) (v r) =
    add (if phaseAt w r (e/3) = e%3 then upper w v r (e/3) else 0)
      (ofNat (coefficient w e r * offset w r (e/3))) := by
  by_cases h : phaseAt w r (e/3) = e%3
  · simp only [CoveringCertifiedLinear.matrix3, coefficient, if_pos h, Nat.one_mul]
    change mul 1 (v r) = add (add (v r) (neg (ofNat (offset w r (e/3))))) (ofNat (offset w r (e/3)))
    rw [mul_one, add_neg_cancel]
  · simp [CoveringCertifiedLinear.matrix3, coefficient, h, zero_mul, zero_add, ofNat]

theorem linear_of_moment (w : LinearWitness) (v : Nat → F3) (e : Nat)
    (hm : sum 10 (fun r => if phaseAt w r (e/3) = e%3 then upper w v r (e/3) else 0) = 0) :
    sum 10 (fun r => mul (CoveringCertifiedLinear.matrix3 w e r) (v r)) =
    CoveringCertifiedLinear.right3 w e := by
  calc
    _ = sum 10 (fun r => add (if phaseAt w r (e/3) = e%3 then upper w v r (e/3) else 0)
        (ofNat (coefficient w e r * offset w r (e/3)))) :=
      sum_congr 10 _ _ (fun r _ => linear_point w v e r)
    _ = sum 10 (fun r => ofNat (coefficient w e r * offset w r (e/3))) := by
      rw [sum_add, hm, zero_add]
    _ = CoveringCertifiedLinear.right3 w e := by
      rw [sum_ofNat]
      unfold CoveringCertifiedLinear.right3 rhs
      have hmod : ∀ n, ofNat (n%3) = ofNat n := by intro n; apply Fin.ext; simp [ofNat]
      rw [hmod, ofNat_total]
      rfl
theorem permutation_lift (c : Fin 17) (z : Fin 10 → Fin 9)
    (hp : ∀ j : Fin 5, (rows.map (fun r => translate (representative c r j) (z r))).Perm (residues ++ [0])) :
    LiftEquations c.val (profile z) (vector z) := by
  constructor
  · intro e he
    apply linear_of_moment
    have hj : e/3 < 5 := by omega
    have ht : e%3 < 3 := Nat.mod_lt _ (by decide)
    exact moments_transport c z hp ⟨e/3,hj⟩ ⟨e%3,ht⟩ false
  · intro j hj t ht
    exact moments_transport c z hp ⟨j,hj⟩ ⟨t,ht⟩ true
theorem no_representative_extension (c : Fin 17) :
    ¬ ∃ x : Fin 10 → Fin 9, CoveringTransforms.Extends (representative c) x := by
  rintro ⟨x,hx⟩
  have he := extension_eligible c x hx
  exact no_digit_lift c.val c.isLt (profile (normalized x)) he
    ⟨vector (normalized x), permutation_lift c (normalized x) (extension_difference_perm c x hx)⟩

end CyclicDigitTransport

#print axioms CyclicDigitTransport.no_representative_extension
