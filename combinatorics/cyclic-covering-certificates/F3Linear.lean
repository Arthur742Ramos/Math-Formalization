module
/- Generic left-nullspace certificate soundness over the three-element field.
   Std only. Arithmetic laws are closed finite proofs; sums use induction. -/
public import Std
public section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
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

/-- A checked left-nullspace multiplier whose scalar product with the
    right-hand side is one rules out every solution, in every dimension. -/
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

/-- Derive any certified linear consequence from a linear system. -/
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

#print axioms left_nullspace_sound
#print axioms certified_consequence
end CoveringF3
