module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

/-!
# Scalar block sizes and row-sampling tolerances
-/

@[expose] public section

open Filter
open scoped Topology

namespace BoundedEdgeRegularSubgraphs

/-- The block size of the amplification step. -/
noncomputable def regularBlockSize (H : ℝ) (k : ℕ) : ℕ := ⌈H * (k : ℝ) * Real.sqrt k⌉₊

/-- A block of order H k^(3/2) has a vanishing row-sampling error for
the tolerance k^(-1/2). -/
theorem eventually_regularBlockSize_bounds_half {H : ℝ} (hH : 1 ≤ H) :
    ∀ᶠ k : ℕ in atTop,
      let m := regularBlockSize H k
      2 ≤ m ∧ H * (k : ℝ) * Real.sqrt k ≤ (m : ℝ) ∧
        (m : ℝ) ≤ 2 * H * (k : ℝ) * Real.sqrt k ∧
        2 * (m : ℝ) * Real.exp (-2 * ((m - 1 : ℕ) : ℝ) * ((Real.sqrt k)⁻¹) ^ 2) < 1 / 2 := by
  let w (k : ℕ) := Real.sqrt (k : ℝ)
  have hpos : 0 < H := zero_lt_one.trans_le hH
  have hW : Tendsto w atTop atTop := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun k : ℕ ↦ 4 * H * w k ^ 3 * Real.exp (-(H * w k))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 3 H hpos).comp hW
    have h' : Tendsto (fun k : ℕ ↦ w k ^ 3 * Real.exp (-(H * w k))) atTop (𝓝 0) := by
      simpa only [Function.comp_def, ← Real.rpow_natCast, Nat.cast_ofNat, neg_mul] using h
    simpa only [mul_zero, mul_assoc] using (tendsto_const_nhds (x := 4 * H)).mul h'
  filter_upwards [eventually_ge_atTop (4 : ℕ), ht.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num)]
    with k hk hsmall
  let m := regularBlockSize H k
  let p := H * (k : ℝ) * w k
  have hk₄ : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hk₀ : (0 : ℝ) < k := by linarith only [hk₄]
  have hw₀ : 0 < w k := Real.sqrt_pos.mpr hk₀
  have hw : (2 : ℝ) ≤ w k := by
    exact (Real.le_sqrt (by norm_num) hk₀.le).2 (by norm_num; exact hk)
  have hp : (2 : ℝ) ≤ p := by
    have hK : 1 ≤ H * (k : ℝ) := one_le_mul_of_one_le_of_one_le hH (by linarith only [hk₄])
    exact hw.trans (le_mul_of_one_le_left hw₀.le hK)
  have hm : p ≤ (m : ℝ) := Nat.le_ceil p
  have hm₂ : 2 ≤ m := by exact_mod_cast hp.trans hm
  have hm' : (m : ℝ) ≤ 2 * H * (k : ℝ) * w k := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ p by linarith only [hp])
    change (m : ℝ) < p + 1 at h
    dsimp only [p] at h hp
    linarith only [h, hp]
  have hPow : (w k) ^ 2 = (k : ℝ) := Real.sq_sqrt hk₀.le
  have hmSub : p / 2 ≤ ((m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    linarith only [hm, hp]
  have hExp : -2 * ((m - 1 : ℕ) : ℝ) * ((w k)⁻¹) ^ 2 ≤ -(H * w k) := by
    have ht := mul_le_mul_of_nonneg_right hmSub (sq_nonneg ((w k)⁻¹))
    have he : p / 2 * ((w k)⁻¹) ^ 2 = H * w k / 2 := by
      dsimp only [p]
      rw [← hPow]
      field_simp [hw₀.ne'] <;> ring
    rw [he] at ht
    linarith only [ht]
  refine ⟨hm₂, hm, hm', ?_⟩
  have hm'' : 2 * (m : ℝ) ≤ 4 * H * w k ^ 3 := by
    rw [← hPow] at hm'
    nlinarith only [hm']
  exact (mul_le_mul hm'' (Real.exp_le_exp.mpr hExp) (Real.exp_nonneg _) (by positivity)).trans_lt hsmall

theorem eventually_regularBlockSize_bounds {H : ℝ} (hH : 1 ≤ H) :
    ∀ᶠ k : ℕ in atTop,
      let m := regularBlockSize H k
      2 ≤ m ∧ H * (k : ℝ) * Real.sqrt k ≤ (m : ℝ) ∧
        (m : ℝ) ≤ 2 * H * (k : ℝ) * Real.sqrt k ∧
        2 * (m : ℝ) * Real.exp (-2 * ((m - 1 : ℕ) : ℝ) * ((Real.sqrt k)⁻¹) ^ 2) < 1 :=
  (eventually_regularBlockSize_bounds_half hH).mono fun _ h ↦
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans (by norm_num)⟩

end BoundedEdgeRegularSubgraphs
