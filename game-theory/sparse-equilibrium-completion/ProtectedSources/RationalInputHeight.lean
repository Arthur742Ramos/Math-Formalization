/- AI-assisted formalization under repository Apache-2.0.
Development value-encoding bounds for canonical rational numerators and
denominators. No arithmetic-operation or solver runtime bound is asserted. -/
module
public import ProtectedSources.RationalFlowEncodingBounds
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

/-- An explicit bound on both canonical integer components; no field supplies
an output-size or complexity conclusion. -/
def RationalInputHeight (q : ℚ) (B : ℕ) : Prop :=
  q.num.natAbs ≤ (Nat.pow 2 B) ∧ q.den ≤ (Nat.pow 2 B)

instance rationalInputHeightDecidable (q : ℚ) (B : ℕ) :
    Decidable (RationalInputHeight q B) := by
  unfold RationalInputHeight
  infer_instance

theorem rational_input_height_mono {q : ℚ} {A B : ℕ}
    (h : RationalInputHeight q A) (hAB : A ≤ B) : RationalInputHeight q B := by
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hAB
  exact ⟨h.1.trans hp, h.2.trans hp⟩

theorem rational_input_height_magnitude {q : ℚ} {B : ℕ}
    (h : RationalInputHeight q B) : |q| ≤ ((Nat.pow 2 B) : ℕ) :=
  (rational_magnitude_le_num_abs q).trans (by exact_mod_cast h.1)

theorem rational_input_height_bits {q : ℚ} {B : ℕ}
    (h : RationalInputHeight q B) : rationalCanonicalEncodingBits q ≤ 2*B+3 := by
  have hn := natural_log2_bits_bound_of_binary_bound q.num.natAbs B h.1
  have hd := natural_log2_bits_bound_of_binary_bound q.den B h.2
  unfold rationalCanonicalEncodingBits
  omega

theorem rational_input_height_zero (B : ℕ) : RationalInputHeight 0 B := by
  have hp : 0 < Nat.pow 2 B := Nat.two_pow_pos B
  simp only [RationalInputHeight, Rat.num_zero, Int.natAbs_zero, Rat.den_zero]
  omega

theorem rational_input_height_nat (n B : ℕ) (hn : n ≤ (Nat.pow 2 B)) :
    RationalInputHeight (n : ℚ) B := by
  have hp : 0 < Nat.pow 2 B := Nat.two_pow_pos B
  simp only [RationalInputHeight, Rat.num_natCast, Int.natAbs_natCast, Rat.den_natCast]
  exact ⟨hn, by omega⟩

theorem rational_input_height_one (B : ℕ) : RationalInputHeight 1 B := by
  have hp : 0 < Nat.pow 2 B := Nat.two_pow_pos B
  exact rational_input_height_nat 1 B (by omega)

theorem rational_input_height_neg {q : ℚ} {B : ℕ}
    (h : RationalInputHeight q B) : RationalInputHeight (-q) B := by
  simpa only [RationalInputHeight, Rat.neg_num, Int.natAbs_neg, Rat.neg_den] using h

theorem rational_input_height_inv {q : ℚ} {B : ℕ}
    (h : RationalInputHeight q B) : RationalInputHeight q⁻¹ B := by
  have hp : 0 < Nat.pow 2 B := Nat.two_pow_pos B
  constructor
  · simp only [Rat.num_inv, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_sign]
    split
    · simp
    · simpa only [one_mul] using h.2
  · simp only [Rat.den_inv]
    split
    · omega
    · exact h.1

theorem rational_input_height_mul {a b : ℚ} {A B : ℕ}
    (ha : RationalInputHeight a A) (hb : RationalInputHeight b B) :
    RationalInputHeight (a*b) (2*(A+B)) := by
  have hd : (a*b).den ≤ (Nat.pow 2 (A+B)) := by
    calc
      _ ≤ a.den*b.den := Nat.le_of_dvd (Nat.mul_pos a.den_pos b.den_pos) (Rat.mul_den_dvd a b)
      _ ≤ ((Nat.pow 2 A))*((Nat.pow 2 B)) := Nat.mul_le_mul ha.2 hb.2
      _ = _ := (Nat.pow_add 2 A B).symm
  have hm : |a*b| ≤ ((Nat.pow 2 (A+B)) : ℕ) := by
    calc
      _ = |a| * |b| := abs_mul a b
      _ ≤ (((Nat.pow 2 A) : ℕ) : ℚ)*(((Nat.pow 2 B) : ℕ) : ℚ) :=
        mul_le_mul (rational_input_height_magnitude ha) (rational_input_height_magnitude hb)
          (abs_nonneg b) (by positivity)
      _ = _ := by exact_mod_cast (Nat.pow_add 2 A B).symm
  constructor
  · simpa only [two_mul] using rational_numerator_binary_bound_from_height (a*b) (A+B) (A+B) hm hd
  · exact hd.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))

theorem rational_input_height_div {a b : ℚ} {A B : ℕ}
    (ha : RationalInputHeight a A) (hb : RationalInputHeight b B) :
    RationalInputHeight (a/b) (2*(A+B)) := by
  simpa only [div_eq_mul_inv] using rational_input_height_mul ha (rational_input_height_inv hb)

theorem rational_input_height_add {a b : ℚ} {A B : ℕ}
    (ha : RationalInputHeight a A) (hb : RationalInputHeight b B) :
    RationalInputHeight (a+b) (2*(A+B)+1) := by
  have hd : (a+b).den ≤ (Nat.pow 2 (A+B)) := by
    calc
      _ ≤ a.den*b.den := Nat.le_of_dvd (Nat.mul_pos a.den_pos b.den_pos) (Rat.add_den_dvd a b)
      _ ≤ ((Nat.pow 2 A))*((Nat.pow 2 B)) := Nat.mul_le_mul ha.2 hb.2
      _ = _ := (Nat.pow_add 2 A B).symm
  have hA : (((Nat.pow 2 A) : ℕ) : ℚ) ≤ ((Nat.pow 2 (A+B)) : ℕ) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_right A B)
  have hB : (((Nat.pow 2 B) : ℕ) : ℚ) ≤ ((Nat.pow 2 (A+B)) : ℕ) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_left B A)
  have hm : |a+b| ≤ ((Nat.pow 2 (A+B+1)) : ℕ) := by
    calc
      _ ≤ |a|+|b| := abs_add_le a b
      _ ≤ (((Nat.pow 2 A) : ℕ) : ℚ)+(((Nat.pow 2 B) : ℕ) : ℚ) :=
        add_le_add (rational_input_height_magnitude ha) (rational_input_height_magnitude hb)
      _ ≤ (((Nat.pow 2 (A+B)) : ℕ) : ℚ)+(((Nat.pow 2 (A+B)) : ℕ) : ℚ) := add_le_add hA hB
      _ = _ := by
        exact_mod_cast (show Nat.pow 2 (A+B)+Nat.pow 2 (A+B) = Nat.pow 2 (A+B+1) by
          rw [show Nat.pow 2 (A+B+1) = Nat.pow 2 (A+B)*2 from rfl]
          omega)
  constructor
  · have hn := rational_numerator_binary_bound_from_height (a+b) (A+B+1) (A+B) hm hd
    convert hn using 1; congr 1; omega
  · exact hd.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))

theorem rational_input_height_sub {a b : ℚ} {A B : ℕ}
    (ha : RationalInputHeight a A) (hb : RationalInputHeight b B) :
    RationalInputHeight (a-b) (2*(A+B)+1) := by
  simpa only [sub_eq_add_neg] using rational_input_height_add ha (rational_input_height_neg hb)

theorem rational_input_height_min {a b : ℚ} {B : ℕ}
    (ha : RationalInputHeight a B) (hb : RationalInputHeight b B) :
    RationalInputHeight (min a b) B := by
  rcases le_total a b with h | h
  · simpa only [min_eq_left h] using ha
  · simpa only [min_eq_right h] using hb

theorem rational_input_height_max {a b : ℚ} {B : ℕ}
    (ha : RationalInputHeight a B) (hb : RationalInputHeight b B) :
    RationalInputHeight (max a b) B := by
  rcases le_total a b with h | h
  · simpa only [max_eq_right h] using hb
  · simpa only [max_eq_left h] using ha

theorem rational_input_height_fin_sum {n B : ℕ} (f : Fin n → ℚ)
    (hf : ∀ i, RationalInputHeight (f i) B) :
    RationalInputHeight (∑ i, f i) (n+B*(n+1)) := by
  let xs := List.ofFn f
  have hn : ∀ a ∈ xs, a.num.natAbs ≤ (Nat.pow 2 B) := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact (hf i).1
  have hd : ∀ a ∈ xs, a.den ≤ (Nat.pow 2 B) := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact (hf i).2
  constructor
  · simpa only [xs, List.sum_ofFn, List.length_ofFn] using
      rational_sum_numerator_binary_bound xs B hn hd
  · have hh := rational_sum_denominator_binary_bound xs B hd
    simp only [xs, List.sum_ofFn, List.length_ofFn] at hh
    exact hh.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (by nlinarith))

end SparseCompletion
