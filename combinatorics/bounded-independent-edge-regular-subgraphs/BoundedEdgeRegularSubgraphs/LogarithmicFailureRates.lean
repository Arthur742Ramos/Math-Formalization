module

public import BoundedEdgeRegularSubgraphs.LogarithmicExtractionScale
import Mathlib.Tactic

/-!
# Uniform failure rates at the logarithmic scale
-/

public section

open Filter Asymptotics
open scoped Topology

namespace BoundedEdgeRegularSubgraphs

theorem tendsto_logarithmicEvenOrder {a : ℝ} (ha : 0 < a) :
    Tendsto (logarithmicEvenOrder a) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_logarithmicEvenOrder_bounds ha,
    hlog.eventually_ge_atTop (max 1 (2 * (k : ℝ) / a))] with n hn hL
  have hL₁ : 1 ≤ Real.log n := (le_max_left _ _).trans hL
  have hL₂ := (div_le_iff₀ ha).1 ((le_max_right _ _).trans hL)
  have hK : (k : ℝ) ≤ a / 2 * Real.log n ^ 2 := by
    nlinarith only [hL₂, mul_nonneg ha.le (mul_nonneg (sub_nonneg.mpr hL₁)
      (show 0 ≤ Real.log n by linarith only [hL₁]))]
  exact_mod_cast hK.trans hn.1

/-- The numerical estimates needed to apply Theorem 3.2 to a trimmed
domain of size at least one half of n to the three-quarter power. -/
theorem eventually_logarithmic_failure_rates {a c μ₀ C : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hμ₀ : 0 < μ₀) (hC : 0 < C) (hac : 192 * a ≤ c / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, (n : ℝ) ^ (3 / 4 : ℝ) / 2 ≤ N →
      let L := Real.log n
      let k := logarithmicEvenOrder a n
      let μ := (k : ℝ) ^ 2 / N
      k ≤ N ∧ μ ≤ μ₀ ∧ 192 / L * k ≤ c * Real.log ((N : ℝ) / (k : ℝ) ^ 2) ∧
        C * μ ^ (3 / 2 : ℝ) + C * Real.exp (-(k : ℝ) * Real.log k / 8) ≤ (n : ℝ)⁻¹ := by
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop := Real.tendsto_log_atTop.comp hcast
  have hlogk : Tendsto (fun n : ℕ ↦ Real.log (logarithmicEvenOrder a n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (hcast.comp (tendsto_logarithmicEvenOrder ha))
  have hlim := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 10)).comp hcast
  have hroot := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp hcast
  have hLpow : ∀ᶠ n : ℕ in atTop, 2 * a ^ 2 * Real.log n ^ 4 ≤ (n : ℝ) ^ (1 / 20 : ℝ) := by
    have h := ((isLittleO_log_rpow_rpow_atTop 4 (by norm_num : (0 : ℝ) < 1 / 20)).comp_tendsto
      hcast).bound (show 0 < (1 / (2 * a ^ 2) : ℝ) by positivity)
    filter_upwards [h] with n hn
    change ‖Real.log n ^ (4 : ℝ)‖ ≤ _ * ‖(n : ℝ) ^ (1 / 20 : ℝ)‖ at hn
    have h4 : Real.log n ^ (4 : ℝ) = Real.log n ^ (4 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.log n) 4
    rw [h4, Real.norm_of_nonneg (show 0 ≤ Real.log n ^ (4 : ℕ) by positivity),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] at hn
    have h₁ := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 2 * a ^ 2)
    refine h₁.trans_eq ?_
    field_simp
  filter_upwards [eventually_logarithmicEvenOrder_bounds ha, hLpow,
    hlim.eventually_le_const hμ₀, hroot.eventually_ge_atTop (2 * C),
    hlog.eventually_ge_atTop (32 / a), hlogk.eventually_ge_atTop 1,
    hcast.eventually_ge_atTop (2 * C),
    eventually_ge_atTop (2 : ℕ),
    (tendsto_logarithmicEvenOrder ha).eventually_ge_atTop (1 : ℕ)] with n hK hPow hμlim hRoot hL hKlog hnC hn hk
  intro N hN
  dsimp only
  change 2 * C ≤ (n : ℝ) ^ (1 / 20 : ℝ) at hRoot
  let L := Real.log n
  let k := logarithmicEvenOrder a n
  let μ := (k : ℝ) ^ 2 / N
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn₀ : (0 : ℝ) < n := zero_lt_one.trans_le hn₁
  have hN₀ : (0 : ℝ) < N := (by positivity : 0 < (n : ℝ) ^ (3 / 4 : ℝ) / 2).trans_le hN
  have hL₀ : 0 < L := (by positivity : 0 < 32 / a).trans_le hL
  have hk₀ : (0 : ℝ) < k := zero_lt_one.trans_le (by exact_mod_cast hk)
  have hμ : μ ≤ (n : ℝ) ^ (-(7 / 10) : ℝ) := by
    have hh : (k : ℝ) ^ 2 ≤ a ^ 2 * L ^ 4 := by
      calc
        _ ≤ (a * L ^ 2) ^ 2 := pow_le_pow_left₀ hk₀.le hK.2 _
        _ = _ := by ring
    change (k : ℝ) ^ 2 / N ≤ _
    apply (div_le_iff₀ hN₀).2
    calc
      _ ≤ (n : ℝ) ^ (1 / 20 : ℝ) / 2 := by linarith only [hh, hPow]
      _ = (n : ℝ) ^ (-(7 / 10) : ℝ) * ((n : ℝ) ^ (3 / 4 : ℝ) / 2) := by
        rw [← mul_div_assoc, ← Real.rpow_add hn₀]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hN (by positivity)
  have hkN : k ≤ N := by
    have hu := Real.rpow_le_rpow_of_exponent_le hn₁ (show (-(7 / 10) : ℝ) ≤ 0 by norm_num)
    rw [Real.rpow_zero] at hu
    have h := (div_le_iff₀ hN₀).1 (hμ.trans hu)
    have hh : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
      nlinarith only [mul_nonneg hk₀.le (sub_nonneg.mpr (show (1 : ℝ) ≤ k by exact_mod_cast hk))]
    have hkn : (k : ℝ) ≤ (N : ℝ) := hh.trans (by simpa only [one_mul] using h)
    exact_mod_cast hkn
  have hLower : L / 2 ≤ Real.log ((N : ℝ) / (k : ℝ) ^ 2) := by
    have hμ₀' : 0 < μ := div_pos (sq_pos_of_pos hk₀) hN₀
    have h := Real.log_le_log hμ₀' hμ
    rw [Real.log_rpow hn₀] at h
    have heq : Real.log μ = -Real.log ((N : ℝ) / (k : ℝ) ^ 2) := by
      dsimp only [μ]
      rw [Real.log_div (sq_pos_of_pos hk₀).ne' hN₀.ne', Real.log_div hN₀.ne' (sq_pos_of_pos hk₀).ne']
      ring
    rw [heq] at h
    linarith only [h, hL₀]
  have hTol : 192 / L * k ≤ c * Real.log ((N : ℝ) / (k : ℝ) ^ 2) := by
    calc
      _ ≤ (192 / L) * (a * L ^ 2) := mul_le_mul_of_nonneg_left hK.2 (by positivity)
      _ = (192 * a) * L := by field_simp <;> ring
      _ ≤ (c / 2) * L := mul_le_mul_of_nonneg_right hac hL₀.le
      _ = c * (L / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hLower hc.le
  have hOne : C * μ ^ (3 / 2 : ℝ) ≤ (n : ℝ)⁻¹ / 2 := by
    have hr := Real.rpow_le_rpow (by dsimp only [μ]; positivity) hμ (by norm_num : 0 ≤ (3 / 2 : ℝ))
    rw [← Real.rpow_mul hn₀.le, show (-(7 / 10) : ℝ) * (3 / 2) = -21 / 20 by norm_num] at hr
    have hroot' := mul_le_mul_of_nonneg_right hRoot
      (Real.rpow_nonneg hn₀.le (-21 / 20 : ℝ))
    rw [← Real.rpow_add hn₀, show (1 / 20 : ℝ) + (-21 / 20) = -1 by norm_num, Real.rpow_neg_one] at hroot'
    linarith only [mul_le_mul_of_nonneg_left hr hC.le, hroot']
  have hTwo : C * Real.exp (-(k : ℝ) * Real.log k / 8) ≤ (n : ℝ)⁻¹ / 2 := by
    have hL' := (div_le_iff₀ ha).1 hL
    have hK' : 16 * L ≤ (k : ℝ) := by
      nlinarith only [hK.1, mul_nonneg hL₀.le (sub_nonneg.mpr hL')]
    have hExp : Real.exp (-(k : ℝ) * Real.log k / 8) ≤ (n : ℝ)⁻¹ ^ 2 := by
      rw [← Real.exp_log hn₀, ← Real.exp_neg, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      nlinarith only [hK', mul_nonneg hk₀.le (sub_nonneg.mpr hKlog)]
    have hInv : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hn₀
    have hC' := mul_le_mul_of_nonneg_right hnC (sq_nonneg ((n : ℝ)⁻¹))
    rw [show (n : ℝ) * ((n : ℝ)⁻¹) ^ 2 = (n : ℝ)⁻¹ by field_simp] at hC'
    linarith only [mul_le_mul_of_nonneg_left hExp hC.le, hC']
  exact ⟨hkN, hμ.trans hμlim, hTol, by linarith only [hOne, hTwo]⟩

end BoundedEdgeRegularSubgraphs
