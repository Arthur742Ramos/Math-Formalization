module

public import BoundedEdgeRegularSubgraphs.FourierBoxRemainder
import Mathlib.Tactic

/-!
# Scalar bounds for the Gaussian quartic on the shrinking box
-/

public section

open Filter
open scoped Topology

namespace BoundedEdgeRegularSubgraphs

/-- Any fixed polynomial factor is dominated by a Gaussian tail in
the logarithm. -/
theorem tendsto_nat_pow_mul_exp_neg_log_sq (p : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ p * Real.exp (-c * Real.log n ^ 2)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hzero := tendsto_inv_atTop_zero.comp hnat
  have hlog := Real.tendsto_log_atTop.comp hnat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
    (.of_forall fun n ↦ by positivity) ?_
  filter_upwards [hlog.eventually_ge_atTop (((p : ℝ) + 1) / c),
    eventually_ge_atTop (1 : ℕ)] with n h hn
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog₀ : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have h' : (p : ℝ) + 1 ≤ c * Real.log n :=
    by simpa only [Function.comp_apply, mul_comm] using (div_le_iff₀ hc).mp h
  have hh : -c * Real.log n ^ 2 ≤ -(((p : ℝ) + 1) * Real.log n) := by
    nlinarith only [mul_le_mul_of_nonneg_right h' hlog₀]
  calc
    _ ≤ (n : ℝ) ^ p * Real.exp (-(((p : ℝ) + 1) * Real.log n)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hh) (by positivity)
    _ = (n : ℝ)⁻¹ := by
      rw [show -(((p : ℝ) + 1) * Real.log n) =
        -((p : ℝ) * Real.log n + Real.log n) by ring, Real.exp_neg, Real.exp_add,
        Real.exp_nat_mul, Real.exp_log hn₀]
      field_simp

/-- The normalized Lipschitz constant for the clipped quartic tends to zero. -/
theorem tendsto_log_cube_div_sqrt_nat :
    Tendsto (fun k : ℕ ↦ Real.log k ^ 3 / Real.sqrt k) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : ℝ)) 3 (by norm_num)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ ↦ (k : ℝ)) atTop atTop)
  change Tendsto (fun k : ℕ ↦ Real.log k ^ (3 : ℝ) / (k : ℝ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) at h
  simpa only [← Real.rpow_natCast, Nat.cast_ofNat, Real.sqrt_eq_rpow] using h

theorem quartic_box_lipschitzRate_le {k : ℕ} (hk : 0 < k)
    {K a : ℝ} (hK : 0 ≤ K) (ha : 0 < a) :
    let r := fourierBoxRadius k
    4 * (2 * r) ^ 3 * K * ((k : ℝ) - 1) * Real.sqrt k * (Real.sqrt (a / k)) ≤
      (32 * K * Real.sqrt a) * (Real.log k ^ 3 / Real.sqrt k) := by
  let r := fourierBoxRadius k
  have hk₀ : (0 : ℝ) < k := by exact_mod_cast hk
  have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : 0 ≤ r := div_nonneg (Real.log_nonneg hk₁) (Real.sqrt_nonneg _)
  calc
    _ ≤ 4 * (2 * r) ^ 3 * K * k * Real.sqrt k * Real.sqrt (a / k) := by
      gcongr
      exact sub_le_self _ zero_le_one
    _ = _ := by
      have hsq : Real.sqrt (k : ℝ) ^ 2 = k := Real.sq_sqrt hk₀.le
      have hcube : Real.sqrt (k : ℝ) ^ 3 = k * Real.sqrt k := by
        rw [show (3 : ℕ) = 2 + 1 by decide, pow_add, hsq, pow_one]
      dsimp only [r, fourierBoxRadius]
      rw [Real.sqrt_div ha.le,
        show 2 * (Real.log k / Real.sqrt k) = (2 * Real.log k) / Real.sqrt k by ring,
        div_pow, hcube]
      field_simp [hk₀.ne', (Real.sqrt_pos.mpr hk₀).ne'] <;> ring

end BoundedEdgeRegularSubgraphs
