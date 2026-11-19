module

public import BoundedEdgeRegularSubgraphs.FourierBoxRemainder
import Mathlib.Tactic

/-!
# Rates in the two Fourier tail estimates
-/

public section

open Filter
open scoped Topology

namespace BoundedEdgeRegularSubgraphs

private theorem tendsto_log_nat_atTop :
    Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)

/-- The Gaussian coordinate tail at the logarithmic box radius dominates
the union over all coordinates. -/
theorem tendsto_nat_mul_exp_neg_log_sq {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.exp (-c * Real.log n ^ 2)) atTop (𝓝 0) := by
  have hzero : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero ?_ ?_
  · exact Eventually.of_forall (fun n ↦ mul_nonneg (Nat.cast_nonneg n) (Real.exp_nonneg _))
  · filter_upwards [tendsto_log_nat_atTop.eventually_ge_atTop (2 / c), eventually_ge_atTop (1 : ℕ)] with n h hn
    have hn₀ : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have h' : (2 : ℝ) ≤ c * Real.log n := by
      have h := (div_le_iff₀ hc).mp h
      simpa only [mul_comm] using h
    have hh : -c * Real.log n ^ 2 ≤ -2 * Real.log n := by
      nlinarith only [mul_le_mul_of_nonneg_right h' hlog]
    calc
      _ ≤ (n : ℝ) * Real.exp (-2 * Real.log n) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hh) hn₀.le
      _ = (n : ℝ)⁻¹ := by
        rw [show -2 * Real.log n = -(Real.log n + Real.log n) by ring, Real.exp_neg, Real.exp_add,
          Real.exp_log hn₀]
        field_simp

/-- The many-bad-edge exponential rate beats the inverse Gaussian
normalization in Lemma B.1. -/
theorem tendsto_exp_many_bad_normalized {c C : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ Real.exp (-c * n * Real.log n ^ 2 + n * Real.log n / 2 + C * n))
      atTop (𝓝 0) := by
  have hzero : Tendsto (fun n : ℕ ↦ Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero ?_ ?_
  · exact Eventually.of_forall (fun _ ↦ Real.exp_nonneg _)
  · filter_upwards [tendsto_log_nat_atTop.eventually_ge_atTop (max (1 / c) (2 * (C + 1)))] with n hn
    have hlog : 0 ≤ Real.log n := (div_nonneg zero_le_one hc.le).trans ((le_max_left _ _).trans hn)
    have hh : (1 : ℝ) ≤ c * Real.log n := by
      have h := (div_le_iff₀ hc).mp ((le_max_left _ _).trans hn)
      simpa only [mul_comm] using h
    have hl : Real.log n / 2 + C + 1 ≤ c * Real.log n ^ 2 := by
      nlinarith only [mul_le_mul_of_nonneg_right hh hlog, (le_max_right _ _).trans hn]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- The logarithm of a factor of the form `(a n³)^L` is negligible
against a fixed linear exponent when `L` is bounded by a multiple of
`(log n)^2` plus a constant. -/
theorem tendsto_exceptional_cover_rate (L : ℕ → ℕ) {a c D E : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hL : ∀ᶠ n in atTop, (L n : ℝ) ≤ D * Real.log n ^ 2 + E) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (a * (n : ℝ) ^ 3) ^ L n * Real.exp (-c * n)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n ^ 3 / (n : ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) 3 zero_lt_one).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
    change Tendsto (fun n : ℕ ↦ Real.log n ^ (3 : ℝ) / (n : ℝ) ^ (1 : ℝ)) atTop (𝓝 0) at h
    simpa only [← Real.rpow_natCast, Nat.cast_ofNat, Real.rpow_one] using h
  let W := (|Real.log a| + 3) * (D + E)
  have hW : 0 ≤ W := mul_nonneg (by positivity) (add_nonneg hD hE)
  have hs : Tendsto (fun n : ℕ ↦ W * (Real.log n ^ 3 / (n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := W)).mul hlog
  have hzero : Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.exp (-(c / 2) * n)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (c / 2) (by positivity)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
    change Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) * Real.exp (-(c / 2) * n)) atTop (𝓝 0) at h
    simpa only [Real.rpow_one] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero ?_ ?_
  · exact Eventually.of_forall (fun _ ↦ by positivity)
  · filter_upwards [hL, hs.eventually_lt_const (show 0 < c / 2 by positivity),
      tendsto_log_nat_atTop.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℕ)] with n hN hsmall hlog₁ hn
    have hn₀ : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have h₁ : Real.log (a * (n : ℝ) ^ 3) ≤ (|Real.log a| + 3) * Real.log n := by
      rw [Real.log_mul ha.ne' (pow_ne_zero _ hn₀.ne'), Real.log_pow]
      push_cast
      nlinarith only [le_abs_self (Real.log a), mul_nonneg (abs_nonneg (Real.log a))
        (sub_nonneg.mpr hlog₁)]
    have h₂ : (L n : ℝ) ≤ (D + E) * Real.log n ^ 2 := by
      have he := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Real.log n ^ 2 by nlinarith only [hlog₁]) hE
      linarith only [he, hN]
    have h₃ : (L n : ℝ) * Real.log (a * (n : ℝ) ^ 3) ≤ W * Real.log n ^ 3 := by
      have h := mul_le_mul h₁ h₂ (Nat.cast_nonneg _) (by positivity)
      calc
        _ ≤ ((|Real.log a| + 3) * Real.log n) * ((D + E) * Real.log n ^ 2) := by
          simpa only [mul_comm (L n : ℝ) (Real.log _)] using h
        _ = _ := by dsimp only [W]; ring
    have hs' : W * Real.log n ^ 3 ≤ c / 2 * n := by
      rw [← mul_div_assoc] at hsmall
      exact ((div_lt_iff₀ hn₀).mp hsmall).le
    have hbase : 0 < a * (n : ℝ) ^ 3 := by positivity
    rw [← Real.exp_log hbase, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hn₀.le
    linarith only [h₃.trans hs']

end BoundedEdgeRegularSubgraphs
