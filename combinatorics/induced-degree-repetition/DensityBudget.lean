module

public import DensityStep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

public section
namespace InducedDegreeRepetition

open Real

/-- Parameter bounds for one round. A fixed sample of length 1024r suffices.
The block size is ⌊r/J⌋+1 and 1−2τ = exp(−c/16384). -/
theorem density_budget (c : ℝ) (J r : ℕ) (hc : 0 < c) (hJ : 0 < J) (hr : J ≤ r)
    (ramseyScale : 8*log 4 ≤ c*J) (big : log 8 ≤ c*r/8) (x : ℝ)
    (lower : exp (c*r/2) ≤ x) (upper : x ≤ exp (2*c*r)) :
    let u := c/(64*J)
    let s := r/J+1
    (4:ℝ)^(s-1) + x^s * exp (-u*r)^(1024*r) <
      x/2 * exp (-c/16384)^(1024*r) := by
  let j := (J:ℝ)
  have jp : 0 < j := Nat.cast_pos.mpr hJ
  have rr : 0 ≤ (r:ℝ) := Nat.cast_nonneg _
  have sJ : ((r/J:ℕ):ℝ)*j ≤ r := by dsimp [j]; exact_mod_cast Nat.div_mul_le_self r J
  have hscale : 8*log 4 ≤ c*j := ramseyScale
  have rlg : ((r/J:ℕ):ℝ)*log 4 ≤ c*r/8 := by
    nlinarith [mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg (r/J)),
      mul_le_mul_of_nonneg_left sJ hc.le]
  have ram : (4:ℝ)^(r/J) ≤ exp (c*r/8) := by
    calc
      _ = exp (((r/J:ℕ):ℝ)*log 4) := by rw [exp_nat_mul,exp_log (by norm_num : (0:ℝ)<4)]
      _ ≤ _ := exp_le_exp.mpr rlg
  let u := c/(64*j)
  have uJ : u * (64*j) = c := div_mul_cancel₀ _ (by positivity)
  have up : 0 < u := div_pos hc (by positivity)
  have block : (((r/J+1:ℕ):ℝ))*j ≤ 2*r := by
    push_cast
    have jle : j ≤ r := by dsimp [j]; exact_mod_cast hr
    linarith
  have coeff : (((r/J+1:ℕ):ℝ))*(2*c) ≤ (1024*r)*u := by
    apply le_of_mul_le_mul_right (a := j) _ jp
    nlinarith [mul_le_mul_of_nonneg_right block (show 0 ≤ 2*c by positivity),
      congrArg (fun z : ℝ => z*(r:ℝ)) uJ]
  have loss : x^(r/J+1) * exp (-u*r)^(1024*r) ≤ 1 := by
    have xx := (pow_le_pow_left₀ ((exp_pos _).le.trans lower) upper (r/J+1))
    calc
      _ ≤ (exp (2*c*r))^(r/J+1) * exp (-u*r)^(1024*r) :=
        mul_le_mul_of_nonneg_right xx (by positivity)
      _ = exp (((r/J+1:ℕ):ℝ)*(2*c*r) + ((1024*r:ℕ):ℝ)*(-u*r)) := by
        rw [exp_add, exp_nat_mul, exp_nat_mul]
      _ ≤ 1 := exp_le_one_iff.mpr (by
        push_cast at coeff ⊢
        nlinarith [mul_le_mul_of_nonneg_right coeff rr])
  have gaps : 8 ≤ exp (5*c*r/16) := (log_le_iff_le_exp (by norm_num)).mp (by
    linarith [mul_nonneg hc.le rr])
  have e1 : 1 ≤ exp (c*r/8) := one_le_exp_iff.mpr (by positivity)
  have compare : exp (c*r/8) + 1 < exp (c*r/2)/2 * exp (-c/16384)^(1024*r) := by
    have split : exp (c*r/2) * exp (-c/16384)^(1024*r) =
        exp (c*r/8) * exp (5*c*r/16) := by
      rw [← exp_nat_mul,← exp_add,← exp_add]
      congr 1
      push_cast
      ring
    nlinarith [mul_le_mul_of_nonneg_left gaps (exp_pos (c*r/8)).le]
  change (4:ℝ)^((r/J+1)-1) + _ < _
  rw [Nat.add_sub_cancel]
  exact (add_le_add ram loss).trans_lt (compare.trans_le
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right lower (by norm_num)) (by positivity)))

end InducedDegreeRepetition
