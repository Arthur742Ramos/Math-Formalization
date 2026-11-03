module
public import RepresentativeEligibility
public import ArithmeticExclusion
public import DigitLemmas
public section
namespace CyclicDigitTransport
open CyclicNormalization CyclicRepresentativeExtension CoveringF3 CoveringProfiles
open CoveringFormalRound3Linear CoveringArithmeticExclusion
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

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

/-- No sixth column extends any of the seventeen literal representatives.
    This is not an assertion that the representatives exhaust all coverings. -/
theorem no_representative_extension (c : Fin 17) :
    ¬ ∃ x : Fin 10 → Fin 9, CoveringTransforms.Extends (representative c) x := by
  rintro ⟨x,hx⟩
  have he := extension_eligible c x hx
  exact no_digit_lift c.val c.isLt (profile (normalized x)) he
    ⟨vector (normalized x), permutation_lift c (normalized x) (extension_difference_perm c x hx)⟩

#print axioms no_representative_extension
#print axioms permutation_lift
#print axioms moments_transport
#print axioms phase_eq
#print axioms upper_eq
end CyclicDigitTransport
