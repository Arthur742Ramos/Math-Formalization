module

public import BoundedEdgeRegularSubgraphs.SampleDriftTail
import Mathlib.Tactic

/-!
# The scalar threshold for candidate sets
-/

public section

open Filter
open scoped Topology

namespace BoundedEdgeRegularSubgraphs

@[expose] noncomputable def candidateDriftRate (k : ℕ) : ℝ := Real.sqrt (Real.log k / k)

theorem tendsto_candidateDriftRate : Tendsto candidateDriftRate atTop (𝓝 0) := by
  have h : Tendsto (fun k : ℕ ↦ Real.log k / (k : ℝ)) atTop (𝓝 0) := by
    have ht := (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) 1 zero_lt_one).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ ↦ (k : ℝ)) atTop atTop)
    change Tendsto (fun k : ℕ ↦ Real.log k ^ (1 : ℝ) / (k : ℝ) ^ (1 : ℝ)) atTop (𝓝 0) at ht
    simpa only [Real.rpow_one] using ht
  change Tendsto (fun n : ℕ ↦ Real.sqrt (Real.log n / (n : ℝ))) atTop (𝓝 0)
  simpa only [Function.comp_def, Real.sqrt_zero] using
    (Real.continuous_sqrt.continuousAt (x := (0 : ℝ))).tendsto.comp h

/-- The maximum drift threshold has the order used in (2.1) and
the conditional Hoeffding bound is sufficiently small. -/
theorem eventually_candidateDriftRates {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∀ᶠ k : ℕ in atTop,
      let z := candidateDriftRate k
      let m := ((k - 1 : ℕ) : ℝ)
      2 * (k : ℝ) * Real.exp (-2 * m * (2 * z) ^ 2) ≤ 1 / 4 ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ a₀ / 2 →
        m * a + 1 + m * (2 * z) ≤ (k : ℝ) * (a + 3 * z) ∧ a + 3 * z ≤ a₀ := by
  have hcast : Tendsto (fun k : ℕ ↦ (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun k : ℕ ↦ Real.log k) atTop atTop := Real.tendsto_log_atTop.comp hcast
  filter_upwards [eventually_ge_atTop (2 : ℕ), hlog.eventually_ge_atTop (1 : ℝ),
    tendsto_candidateDriftRate.eventually_lt_const (show 0 < a₀ / 6 by positivity)] with k hk hL hz₁
  let z := candidateDriftRate k
  let m := ((k - 1 : ℕ) : ℝ)
  have hk₂ : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk₁ : (1 : ℝ) ≤ k := by linarith
  have hk₀ : (0 : ℝ) < k := by linarith
  have hm : m = (k : ℝ) - 1 := by dsimp only [m]; rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hm₁ : (k : ℝ) / 2 ≤ m := by linarith only [hm, hk₂]
  have hm₂ : m ≤ k := by linarith only [hm]
  have hz₀ : 0 ≤ z := Real.sqrt_nonneg _
  have hz : z ^ 2 = Real.log k / (k : ℝ) := Real.sq_sqrt (by positivity)
  have h₁ : 1 ≤ (k : ℝ) * z := by
    apply (sq_le_sq₀ zero_le_one (by positivity)).mp
    rw [one_pow, mul_pow, hz]
    have hprod := mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hk₁)
    have hll : 1 ≤ (k : ℝ) * Real.log k := by nlinarith only [hL, hk₁, hprod]
    exact hll.trans_eq (by field_simp [hk₀.ne'])
  refine ⟨?_, ?_⟩
  · have h₄ : -2 * m * (2 * z) ^ 2 ≤ -4 * Real.log k := by
      have hs := mul_le_mul_of_nonneg_right hm₁ (sq_nonneg z)
      have he : (k : ℝ) * z ^ 2 = Real.log k := by rw [hz]; field_simp [hk₀.ne']
      nlinarith only [hs, he]
    calc
      _ ≤ 2 * (k : ℝ) * Real.exp (-4 * Real.log k) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h₄) (by positivity)
      _ = 2 / (k : ℝ) ^ 3 := by
        rw [show -4 * Real.log k = -((4 : ℕ) * Real.log k) by push_cast; ring,
          Real.exp_neg, Real.exp_nat_mul, Real.exp_log hk₀]
        field_simp [hk₀.ne'] <;> ring
      _ ≤ _ := by
        have hh := pow_le_pow_left₀ (by norm_num : 0 ≤ (2 : ℝ)) hk₂ 3
        have hD : 0 < (k : ℝ) ^ 3 := by positivity
        apply (div_le_iff₀ hD).mpr
        nlinarith only [hh]
  · intro a ha ha'
    have hn := mul_le_mul_of_nonneg_right hm₂ ha
    have hzn := mul_le_mul_of_nonneg_right hm₂ (show 0 ≤ 2 * z by positivity)
    exact ⟨by linarith only [h₁, hn, hzn], by linarith only [ha', hz₁]⟩

end BoundedEdgeRegularSubgraphs
