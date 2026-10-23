/- AI-assisted formalization under the repository Apache-2.0 license.
Magnitude and numerator bounds for actual rational list sums, supplementing
the denominator bounds. These value-size statements do not bound primitive
arithmetic, normalization/gcd cost, allocation or solver runtime. -/
module
public import ProtectedSources.RationalDenominatorGrowth
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic
@[expose] public section
namespace SparseCompletion

theorem rational_num_abs_identity (q : ℚ) :
    (q.num.natAbs : ℚ)= |q| *(q.den : ℚ) := by
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hn : (q.num : ℚ)=q*(q.den : ℚ) := (div_eq_iff hd).mp q.num_div_den
  calc
    _ = |(q.num : ℚ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
    _ = |q*(q.den : ℚ)| := congrArg abs hn
    _ = _ := by
      have hp : (0 : ℚ) < (q.den : ℚ) := by exact_mod_cast q.den_pos
      rw [abs_mul,abs_of_pos hp]

theorem rational_magnitude_le_num_abs (q : ℚ) : |q| ≤ (q.num.natAbs : ℚ) := by
  rw [rational_num_abs_identity]
  have hd : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  nlinarith [abs_nonneg q]

theorem rational_sum_magnitude_bound (xs : List ℚ) (N : ℕ)
    (hb : ∀ a ∈ xs, a.num.natAbs ≤ N) :
    |xs.sum| ≤ (xs.length : ℚ)*(N : ℚ) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha : |a| ≤ (N : ℚ) := (rational_magnitude_le_num_abs a).trans (by exact_mod_cast hb a List.mem_cons_self)
    have ht := ih (fun b h => hb b (List.mem_cons_of_mem a h))
    simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    exact (abs_add_le a xs.sum).trans (by nlinarith)

theorem rational_sum_numerator_product_bound (xs : List ℚ) (N : ℕ)
    (hb : ∀ a ∈ xs, a.num.natAbs ≤ N) :
    xs.sum.num.natAbs ≤ xs.length*N*rationalDenominatorProduct xs := by
  have hm := rational_sum_magnitude_bound xs N hb
  have hd := rational_sum_denominator_le_product xs
  have hdn : (0 : ℚ) ≤ xs.sum.den := by positivity
  have hdc : (xs.sum.den : ℚ) ≤ rationalDenominatorProduct xs := by exact_mod_cast hd
  have hn := rational_num_abs_identity xs.sum
  have hbound : (xs.sum.num.natAbs : ℚ) ≤
      (xs.length : ℚ)*(N : ℚ)*(rationalDenominatorProduct xs : ℚ) := by
    rw [hn]
    exact (mul_le_mul_of_nonneg_right hm hdn).trans
      (mul_le_mul_of_nonneg_left hdc (by positivity))
  exact_mod_cast hbound

theorem rational_sum_numerator_power_bound (xs : List ℚ) (N D : ℕ)
    (hn : ∀ a ∈ xs, a.num.natAbs ≤ N) (hd : ∀ a ∈ xs, a.den ≤ D) :
    xs.sum.num.natAbs ≤ xs.length*N*Nat.pow D xs.length :=
  (rational_sum_numerator_product_bound xs N hn).trans
    (Nat.mul_le_mul_left (xs.length*N) (rational_denominator_product_power xs D hd))


theorem rational_sum_numerator_binary_bound (xs : List ℚ) (B : ℕ)
    (hn : ∀ a ∈ xs, a.num.natAbs ≤ Nat.pow 2 B)
    (hd : ∀ a ∈ xs, a.den ≤ Nat.pow 2 B) :
    xs.sum.num.natAbs ≤ Nat.pow 2 (xs.length+B*(xs.length+1)) := by
  have hh := rational_sum_numerator_power_bound xs (Nat.pow 2 B) (Nat.pow 2 B) hn hd
  have hlen : xs.length ≤ Nat.pow 2 xs.length := Nat.le_of_lt Nat.lt_two_pow_self
  have he : xs.length+B+B*xs.length=xs.length+B*(xs.length+1) := by ring
  calc
    _ ≤ xs.length*Nat.pow 2 B*Nat.pow (Nat.pow 2 B) xs.length := hh
    _ ≤ Nat.pow 2 xs.length*Nat.pow 2 B*Nat.pow (Nat.pow 2 B) xs.length :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hlen)
    _ = Nat.pow 2 (xs.length+B+B*xs.length) := by
      have h1 := Nat.pow_add 2 xs.length B
      have h2 := Nat.pow_mul 2 B xs.length
      have h3 := Nat.pow_add 2 (xs.length+B) (B*xs.length)
      exact (congrArg₂ Nat.mul h1.symm h2.symm).trans h3.symm
    _ = _ := congrArg (Nat.pow 2) he

theorem rational_sum_numerator_bits (xs : List ℚ) (B : ℕ)
    (hn : ∀ a ∈ xs, a.num.natAbs ≤ Nat.pow 2 B)
    (hd : ∀ a ∈ xs, a.den ≤ Nat.pow 2 B) :
    Nat.log2 xs.sum.num.natAbs+1 ≤ xs.length+B*(xs.length+1)+1 := by
  by_cases hz : xs.sum.num.natAbs=0
  · simp only [hz,Nat.log2_zero,zero_add]
    omega
  · have hh := rational_sum_numerator_binary_bound xs B hn hd
    have hp : Nat.pow 2 (xs.length+B*(xs.length+1)) <
        Nat.pow 2 (xs.length+B*(xs.length+1)+1) :=
      Nat.pow_lt_pow_succ Nat.one_lt_two
    have hl := (Nat.log2_lt hz).mpr (hh.trans_lt hp)
    omega

end SparseCompletion
