/- AI-assisted formalization under the repository Apache-2.0 license.
A denominator-only encoding foundation for cached rational prefix sums.
This does not bound numerators or prove any primitive/solver bit complexity. -/
module
public import RationalPrefixScan
public import Mathlib.Data.Rat.Lemmas
@[expose] public section
namespace SparseCompletion

def rationalDenominatorProduct (xs : List ℚ) : ℕ :=
  xs.foldr (fun a n => Nat.mul a.den n) 1

theorem rational_denominator_product_positive (xs : List ℚ) :
    0 < rationalDenominatorProduct xs := by
  induction xs with
  | nil => exact Nat.zero_lt_one
  | cons a xs ih =>
    change 0 < Nat.mul a.den (rationalDenominatorProduct xs)
    exact Nat.mul_pos (Rat.den_pos a) ih

theorem rational_sum_denominator_divides (xs : List ℚ) :
    xs.sum.den ∣ rationalDenominatorProduct xs := by
  induction xs with
  | nil => simp [rationalDenominatorProduct]
  | cons a xs ih =>
    change (a+xs.sum).den ∣ Nat.mul a.den (rationalDenominatorProduct xs)
    exact (Rat.add_den_dvd a xs.sum).trans (Nat.mul_dvd_mul_left a.den ih)

theorem rational_sum_denominator_le_product (xs : List ℚ) :
    xs.sum.den ≤ rationalDenominatorProduct xs :=
  Nat.le_of_dvd (rational_denominator_product_positive xs)
    (rational_sum_denominator_divides xs)

theorem rational_denominator_product_power (xs : List ℚ) (D : ℕ)
    (hb : ∀ a ∈ xs, a.den ≤ D) :
    rationalDenominatorProduct xs ≤ Nat.pow D xs.length := by
  induction xs generalizing D with
  | nil => exact Nat.le_refl 1
  | cons a xs ih =>
    have ha := hb a List.mem_cons_self
    have ht := ih D (fun b h => hb b (List.mem_cons_of_mem a h))
    change Nat.mul a.den (rationalDenominatorProduct xs) ≤ Nat.pow D (xs.length+1)
    have hp : Nat.pow D (xs.length+1) = Nat.pow D xs.length*D := rfl
    rw [hp]
    exact (Nat.mul_le_mul ha ht).trans_eq (Nat.mul_comm _ _)

theorem rational_sum_denominator_power (xs : List ℚ) (D : ℕ)
    (hb : ∀ a ∈ xs, a.den ≤ D) :
    xs.sum.den ≤ Nat.pow D xs.length :=
  (rational_sum_denominator_le_product xs).trans
    (rational_denominator_product_power xs D hb)


theorem rational_sum_denominator_binary_bound (xs : List ℚ) (B : ℕ)
    (hb : ∀ a ∈ xs, a.den ≤ Nat.pow 2 B) :
    xs.sum.den ≤ Nat.pow 2 (B*xs.length) := by
  have hh := rational_sum_denominator_power xs (Nat.pow 2 B) hb
  have hp : Nat.pow 2 (B*xs.length) = Nat.pow (Nat.pow 2 B) xs.length :=
    Nat.pow_mul 2 B xs.length
  exact hh.trans_eq hp.symm


theorem rational_sum_denominator_bits (xs : List ℚ) (B : ℕ)
    (hb : ∀ a ∈ xs, a.den ≤ Nat.pow 2 B) :
    Nat.log2 xs.sum.den+1 ≤ B*xs.length+1 := by
  have hd : xs.sum.den ≠ 0 := (Rat.den_pos xs.sum).ne'
  have hp : Nat.pow 2 (B*xs.length) < Nat.pow 2 (B*xs.length+1) :=
    Nat.pow_lt_pow_succ Nat.one_lt_two
  have hl : xs.sum.den < Nat.pow 2 (B*xs.length+1) :=
    (rational_sum_denominator_binary_bound xs B hb).trans_lt hp
  have hh : Nat.log2 xs.sum.den < B*xs.length+1 := (Nat.log2_lt hd).mpr hl
  omega

end SparseCompletion
