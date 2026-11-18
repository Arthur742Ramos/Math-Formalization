module

public import BoundedEdgeRegularSubgraphs.FourierSmallBoxBound
public import BoundedEdgeRegularSubgraphs.FourierBoxRemainder
import Mathlib.Tactic

/-!
# The uniform cost of the shrinking Fourier box
-/

public section

open Filter Matrix
open scoped BigOperators Topology

namespace BoundedEdgeRegularSubgraphs

/-- The shrinking radius meets the Taylor hypotheses, with remainder at
most one for every available edge set. -/
theorem eventually_degreeFourierLocalError_le_one :
    ∀ᶠ k : ℕ in atTop,
      0 ≤ fourierBoxRadius k ∧ 2 * fourierBoxRadius k ≤ 1 / 4 ∧
      ∀ (A : Finset (Edge (Fin k))) (q : Edge (Fin k) → Set.Icc (0 : ℝ) 1),
        ∀ t ∈ realPhaseBox (α := Fin k) (fourierBoxRadius k),
          ‖degreeFourierLocalError A q t‖ ≤ 1 := by
  -- The scalar Taylor bound is independent of the size of the vertex set.
  obtain ⟨C, hC, hT⟩ := bernoulli_log_expansion
  have hR : Tendsto (fun k : ℕ ↦ C * ((k : ℝ) ^ 2 * (2 * fourierBoxRadius k) ^ 5)) atTop (𝓝 0) :=
    by simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul fourierBox_fifth_error_tendsto_zero
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    fourierBoxRadius_tendsto_zero.eventually_lt_const (show (0 : ℝ) < 1 / 8 by norm_num),
    hR.eventually_lt_const zero_lt_one] with k hk hRad hBound
  have hr₀ : 0 ≤ fourierBoxRadius k :=
    div_nonneg (Real.log_nonneg (show (1 : ℝ) ≤ k by exact_mod_cast hk)) (Real.sqrt_nonneg _)
  have hr' : 2 * fourierBoxRadius k ≤ 1 / 4 := by linarith only [hRad]
  refine ⟨hr₀, hr', fun A q t ht ↦ ?_⟩
  unfold degreeFourierLocalError
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ e ∈ A, C * |t e.val.1 + t e.val.2| ^ 5 := by
      apply Finset.sum_le_sum
      intro e _
      let z := ((t e.val.1 + t e.val.2 : ℝ) : ℂ) * Complex.I
      have hz : ‖z‖ = |t e.val.1 + t e.val.2| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have hz' : ‖z‖ ≤ 1 / 4 := by
        rw [hz]
        exact (abs_add_le _ _).trans (by linarith only [ht e.val.1, ht e.val.2, hr'])
      have h := hT (q e : ℝ) z (q e).property hz'
      rwa [hz] at h
    _ ≤ C * ∑ e : Edge (Fin k), |t e.val.1 + t e.val.2| ^ 5 := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ by positivity)) hC.le
    _ ≤ C * ((k : ℝ) ^ 2 * (2 * fourierBoxRadius k) ^ 5) :=
      mul_le_mul_of_nonneg_left (sum_edge_fifth_le_fourierBox k t ht) hC.le
    _ ≤ _ := hBound.le

/-- If the covariance lower bound is at least linear in the order, the
small-box exponential cost is bounded by a constant independent of the array. -/
theorem eventually_uniform_fourierBox_cost {a : ℝ} (ha : 0 < a) :
    ∀ᶠ k : ℕ in atTop, ∀ lower : ℝ, a * k ≤ lower →
      let r := fourierBoxRadius k
      let K := (1 / 96 : ℝ)
      let κ := 4 * (2 * r) ^ 3 * K * ((k : ℝ) - 1) * Real.sqrt k * Real.sqrt lower⁻¹
      1 + 24 * K * ((k : ℝ) - 1) * k * lower⁻¹ ^ 2 + κ ^ 2 / 2 ≤ 2 + 1 / (4 * a ^ 2) := by
  have H : Tendsto (fun k : ℕ ↦ Real.log k ^ 3 / Real.sqrt k) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : ℝ)) 3 (by norm_num)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ ↦ (k : ℝ)) atTop atTop)
    change Tendsto (fun k : ℕ ↦ Real.log k ^ (3 : ℝ) / (k : ℝ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) at h
    simpa only [← Real.rpow_natCast, Nat.cast_ofNat, Real.sqrt_eq_rpow] using h
  let K := (1 / 96 : ℝ)
  have hsmall : Tendsto (fun k : ℕ ↦ (32 * K * (Real.sqrt a)⁻¹) *
      (Real.log k ^ 3 / Real.sqrt k)) atTop (𝓝 0) :=
    by simpa only [mul_zero] using tendsto_const_nhds.mul H
  filter_upwards [eventually_ge_atTop (1 : ℕ), hsmall.eventually_lt_const zero_lt_one] with k hk hs
  intro lower hlow
  let r := fourierBoxRadius k
  let κ := 4 * (2 * r) ^ 3 * K * ((k : ℝ) - 1) * Real.sqrt k * Real.sqrt lower⁻¹
  have hk₀ : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlower : 0 < lower := (mul_pos ha hk₀).trans_le hlow
  have hr : 0 ≤ r := div_nonneg (Real.log_nonneg hk₁) (Real.sqrt_nonneg _)
  have hi : lower⁻¹ ≤ (a * (k : ℝ))⁻¹ := inv_anti₀ (mul_pos ha hk₀) hlow
  have hsqrt : Real.sqrt k * Real.sqrt lower⁻¹ ≤ (Real.sqrt a)⁻¹ := by
    refine (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hi) (Real.sqrt_nonneg _)).trans_eq ?_
    rw [Real.sqrt_inv, Real.sqrt_mul ha.le]
    field_simp [(Real.sqrt_pos.mpr ha).ne', (Real.sqrt_pos.mpr hk₀).ne']
  have hκ : 0 ≤ κ := by
    dsimp only [κ, K]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hk₁))
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hκ' : κ ≤ 1 := by
    have hh : κ ≤ 4 * (2 * r) ^ 3 * K * k * (Real.sqrt a)⁻¹ := by
      dsimp only [κ]
      rw [mul_assoc (4 * (2 * r) ^ 3 * K * ((k : ℝ) - 1))]
      apply mul_le_mul _ hsqrt (by positivity) (by dsimp only [K]; positivity)
      exact mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one) (by dsimp only [K]; positivity)
    refine hh.trans ?_
    have he : 4 * (2 * r) ^ 3 * K * k * (Real.sqrt a)⁻¹ =
        (32 * K * (Real.sqrt a)⁻¹) * (Real.log k ^ 3 / Real.sqrt k) := by
      dsimp only [r, fourierBoxRadius]
      have hsq := Real.sq_sqrt hk₀.le
      have hcube : Real.sqrt (k : ℝ) ^ 3 = k * Real.sqrt k := by
        rw [show (3 : ℕ) = 2 + 1 by decide, pow_add, hsq, pow_one]
      rw [show 2 * (Real.log k / Real.sqrt k) = (2 * Real.log k) / Real.sqrt k by ring,
        div_pow, hcube]
      field_simp [hk₀.ne', (Real.sqrt_pos.mpr hk₀).ne'] <;> ring
    rw [he]
    exact hs.le
  have hmean : 24 * K * ((k : ℝ) - 1) * k * lower⁻¹ ^ 2 ≤ 1 / (4 * a ^ 2) := by
    have hpow := pow_le_pow_left₀ (inv_nonneg.mpr hlower.le) hi 2
    have hkk : ((k : ℝ) - 1) * k ≤ (k : ℝ) ^ 2 := by nlinarith only [hk₀.le]
    have h := mul_le_mul hkk hpow (by positivity) (sq_nonneg _)
    have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ 24 * K by dsimp only [K]; positivity)
    have he : 24 * K * ((k : ℝ) ^ 2 * ((a * k)⁻¹) ^ 2) = 1 / (4 * a ^ 2) := by
      dsimp only [K]
      field_simp [ha.ne', hk₀.ne']
      ring
    rw [he] at h'
    linarith only [h']
  have hκ₂ := pow_le_pow_left₀ hκ hκ' 2
  change 1 + 24 * K * ((k : ℝ) - 1) * k * lower⁻¹ ^ 2 + κ ^ 2 / 2 ≤ _
  linarith only [hκ₂, hmean]

end BoundedEdgeRegularSubgraphs
