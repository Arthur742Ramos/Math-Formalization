module

public import AdjustmentLengths
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Edit

open Filter
open scoped Topology

theorem edit_rates (M : ℕ) (w β : ℝ) (hw : 0 < w) (w1 : w ≤ 1) (hb : 0 < β) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ∀ (L e ℓ r : ℕ), L ≤ M → e ≤ 4*r → (ℓ:ℝ) ≤ a*r →
      ((L:ℝ)+1)^(e+ℓ)*(Real.exp (-budget L*r)/w^ℓ) ≤ Real.exp (-(r:ℝ)) ∧
      ((L:ℝ)+1)^ℓ * Real.exp (-β*r) ≤ Real.exp (-(β/2)*r) := by
  let b := Real.log ((M:ℝ)+1)-Real.log w+1
  have logw := Real.log_nonpos hw.le w1
  have logM := Real.log_nonneg (show 1 ≤ (M:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) M])
  have bp : 0 < b := by dsimp [b]; linarith
  let a := min 1 (min (1/b) (β/(2*b)))
  have ap : 0 < a := by dsimp [a]; positivity
  refine ⟨a,ap,min_le_left ..,?_⟩
  intro L e ℓ r hL he hℓ
  have h₁ := (min_le_right 1 _).trans (min_le_left (1/b) (β/(2*b)))
  have h₂ := (min_le_right 1 _).trans (min_le_right (1/b) (β/(2*b)))
  have ab : a*b ≤ 1 := (le_div_iff₀ bp).mp h₁
  have ab' : a*b ≤ β/2 := by have := (le_div_iff₀ (by positivity : 0<2*b)).mp h₂; change a*(2*b) ≤ β at this; linarith
  have lg := Real.log_le_log (show (0:ℝ)<L+1 by positivity)
    (show (L:ℝ)+1 ≤ M+1 by exact_mod_cast Nat.succ_le_succ hL)
  have ln := Real.log_nonneg (show 1 ≤ (L:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) L])
  have eqp (n : ℕ) : ((L:ℝ)+1)^n = Real.exp (n*Real.log ((L:ℝ)+1)) := by
    rw [Real.exp_nat_mul,Real.exp_log (by positivity)]
  have eqw : w^ℓ = Real.exp (ℓ*Real.log w) := by rw [Real.exp_nat_mul,Real.exp_log hw]
  have eh : (e:ℝ) ≤ 4*(r:ℝ) := by exact_mod_cast he
  have cost := (mul_le_mul_of_nonneg_right hℓ bp.le)
  have first := mul_le_mul_of_nonneg_right ab (Nat.cast_nonneg r : (0:ℝ) ≤ r)
  have second := mul_le_mul_of_nonneg_right ab' (Nat.cast_nonneg r : (0:ℝ) ≤ r)
  have scale (z : ℝ) (hz : z ≤ b) : (ℓ:ℝ)*z ≤ ℓ*b := mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg _)
  constructor
  · rw [eqp,eqw,← Real.exp_sub,← Real.exp_add,Real.exp_le_exp,Nat.cast_add]
    dsimp [budget]
    nlinarith only [mul_le_mul_of_nonneg_right eh ln,cost,first,scale _ (by dsimp [b]; linarith : Real.log ((L:ℝ)+1)-Real.log w ≤ b)]
  · rw [eqp,← Real.exp_add,Real.exp_le_exp]
    nlinarith only [cost,second,scale _ (by dsimp [b]; linarith : Real.log ((L:ℝ)+1) ≤ b)]

theorem total_failure_rate (p : ℕ) (β ε : ℝ) (hb : 0 < β) (he : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, (r:ℝ)^p * (Real.exp (-(r:ℝ)) + r*Real.exp (-(β/2)*r)) ≤ ε := by
  have small (v : ℝ) (hv : 0 < v) (k : ℕ) :
      Tendsto (fun r : ℕ => (r:ℝ)^k*Real.exp (-v*r)) atTop (𝓝 0) := by
    have t := tendsto_pow_const_div_const_pow_of_one_lt k (Real.one_lt_exp_iff.mpr hv)
    apply t.congr
    intro r
    rw [← Real.exp_nat_mul,div_eq_mul_inv,← Real.exp_neg]
    congr 2
    ring
  have t := (small 1 zero_lt_one p).add (small (β/2) (by positivity) (p+1))
  rw [add_zero] at t
  filter_upwards [t.eventually_le_const he] with r hr
  simpa only [Pi.add_apply,neg_one_mul,pow_succ,mul_add,mul_assoc] using hr

end InducedDegreeRepetition.Edit
