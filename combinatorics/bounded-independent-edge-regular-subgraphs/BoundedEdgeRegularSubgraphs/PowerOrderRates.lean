module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

/-!
# Rounding power-law orders and comparing their failure exponents
-/

public section

open Filter

namespace BoundedEdgeRegularSubgraphs

theorem eventually_floor_power_order_bounds {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop, let x := a * (n : ℝ) ^ s
      x / 2 ≤ (⌊x⌋₊ : ℝ) ∧ (⌊x⌋₊ : ℝ) ≤ x := by
  have ht := (tendsto_rpow_atTop hs).comp (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  filter_upwards [ht.eventually_ge_atTop (2 / a)] with n hn
  intro x
  have hh := (div_le_iff₀ ha).1 hn
  have hx : 2 ≤ x := by simpa only [x, mul_comm a, Function.comp_apply] using hh
  exact ⟨by linarith only [hx, Nat.lt_floor_add_one x],
    Nat.floor_le ((by norm_num : (0 : ℝ) ≤ 2).trans hx)⟩

theorem tendsto_floor_power_order {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    Tendsto (fun n : ℕ ↦ ⌊a * (n : ℝ) ^ s⌋₊) atTop atTop := by
  have ht := (tendsto_rpow_atTop hs).comp (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_floor_power_order_bounds ha hs,
    ht.eventually_ge_atTop (2 * (k : ℝ) / a)] with n hn hk
  have hh := (div_le_iff₀ ha).1 hk
  have hx : (k : ℝ) ≤ a * (n : ℝ) ^ s / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    simpa only [mul_comm, Function.comp_apply] using hh
  exact_mod_cast hx.trans hn.1

theorem exp_failure_le_of_power_order {a c s n k : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    (hn : 0 < n) (hk : 0 < k) (hSize : k ≤ a * n ^ s) :
    Real.exp (-c * n / k ^ (3 / 2 : ℝ)) ≤
      Real.exp (-(c / a ^ (3 / 2 : ℝ)) * n ^ (1 - s * (3 / 2))) := by
  have hpow := Real.rpow_le_rpow hk.le hSize (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rw [Real.mul_rpow ha.le (Real.rpow_nonneg hn.le _), ← Real.rpow_mul hn.le] at hpow
  have hb : c * n / (a ^ (3 / 2 : ℝ) * n ^ (s * (3 / 2))) ≤ c * n / k ^ (3 / 2 : ℝ) :=
    div_le_div_of_nonneg_left (mul_nonneg hc hn.le) (Real.rpow_pos_of_pos hk _) hpow
  have he : c * n / (a ^ (3 / 2 : ℝ) * n ^ (s * (3 / 2))) =
      c / a ^ (3 / 2 : ℝ) * n ^ (1 - s * (3 / 2)) := by
    rw [Real.rpow_sub hn, Real.rpow_one]
    ring
  rw [he] at hb
  exact Real.exp_le_exp.mpr (by simpa only [neg_mul, neg_div] using neg_le_neg hb)

end BoundedEdgeRegularSubgraphs
