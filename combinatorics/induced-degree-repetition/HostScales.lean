module

public import SimultaneousAdjustment
public import Reservoirs
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Sampling

open Filter Finset OpenProblems
open scoped Topology Classical
variable {V : Type*}

theorem polynomial_below_exp (d C : ℝ) (dpos : 0 < d) (cp : 0 < C) (k : ℕ) :
    ∀ᶠ r : ℕ in atTop, C*(r:ℝ)^k ≤ Real.exp (d*r) := by
  have lim := tendsto_pow_const_div_const_pow_of_one_lt k (Real.one_lt_exp_iff.mpr dpos)
  filter_upwards [lim.eventually_le_const (show 0 < 1/C by positivity)] with r hr
  rw [← Real.exp_nat_mul] at hr
  have h := (div_le_iff₀ (Real.exp_pos _)).mp hr
  rw [mul_comm (1/C),mul_one_div,le_div_iff₀ cp] at h
  simpa only [mul_comm] using h

theorem inherited_core (G : SimpleGraph V) (B : Finset V) (r : ℕ) (u τ c : ℝ)
    (growth : Real.exp (c*r) ≤ B.card) (cuts : CutBounds G B (B.card*Real.exp (-u*r)) τ) :
    Core G B r (min u (c/2)) τ (c/2) := by
  let v := min u (c/2)
  have h := min_le_right u (c/2)
  have le := min_le_left u (c/2)
  constructor
  · apply le_trans _ (mul_le_mul_of_nonneg_right growth (Real.exp_pos _).le)
    rw [← Real.exp_add,Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_right h (Nat.cast_nonneg r : (0:ℝ)≤r)]
  · intro X hx Y hy dis hX hY b
    have small : (B.card:ℝ)*Real.exp (-u*r) ≤ B.card*Real.exp (-(min u (c/2))*r) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg le) (Nat.cast_nonneg _))) (Nat.cast_nonneg _)
    exact cuts X hx Y hy dis (small.trans hX) (small.trans hY) b

theorem pool_sizes (M t : ℕ) (ht : 0 < t) (size : 4*t ≤ M) :
    let b := M/(2*t)
    0 < b ∧ t*b + M/2 ≤ M ∧ M ≤ 4*t*b ∧ M ≤ 3*(M/2) ∧ b ≤ M/2 := by
  dsimp only
  have den : 0 < 2*t := by omega
  have lo : 1 ≤ M/(2*t) := (Nat.le_div_iff_mul_le den).mpr (by omega)
  have upper := Nat.mul_div_le M (2*t)
  have rem := Nat.mod_lt M den
  have div := Nat.mod_add_div M (2*t)
  have size' := Nat.mul_le_mul_left (2*t) lo
  have half : t*(M/(2*t)) ≤ M/2 := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr (by nlinarith only [upper])
  have tb := Nat.mul_le_mul_right (M/(2*t)) ht
  refine ⟨lo,by omega,?_,by omega,by simpa using tb.trans half⟩
  nlinarith only [rem,div,size']

theorem pool_large (M b t r : ℕ) (u : ℝ) (le : M ≤ 4*t*b)
    (cut : 4*(t:ℝ) ≤ Real.exp ((u/16)*r)) :
    (M:ℝ)*Real.exp (-u*r/16) ≤ b := by
  have g := mul_le_mul_of_nonneg_right cut (Nat.cast_nonneg b : (0:ℝ) ≤ b)
  have e : (M:ℝ) ≤ 4*(t:ℝ)*b := by exact_mod_cast le
  rw [show -u*(r:ℝ)/16 = -((u/16)*r) by ring,Real.exp_neg,← div_eq_mul_inv,div_le_iff₀ (Real.exp_pos _)]
  linarith only [e,g]

end InducedDegreeRepetition.Sampling
