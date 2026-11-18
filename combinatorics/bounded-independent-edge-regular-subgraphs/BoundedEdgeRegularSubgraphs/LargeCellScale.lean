module

public import BoundedEdgeRegularSubgraphs.BlockSizeRates
import Mathlib.Tactic

/-!
# The exponent in the large-cell theorem
-/

public section

open Filter

namespace BoundedEdgeRegularSubgraphs

/-- At orders of size n^(2/(s+3)), a large cell in any half-sized
remainder contains a full block of order H k^(3/2). -/
theorem exists_largeCell_blockScale {s c₀ H : ℝ} (hs : 0 ≤ s) (hc : 0 < c₀) (hH : 1 ≤ H) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ k : ℕ in atTop,
      ∀ n M : ℕ, (k : ℝ) ≤ a * (n : ℝ) ^ (2 / (s + 3)) → n ≤ 2 * M →
        (regularBlockSize H k : ℝ) ≤ c₀ * (M : ℝ) * ((Real.sqrt k)⁻¹) ^ s := by
  let z := (s + 3) / 2
  let a := (c₀ / (4 * H)) ^ (1 / z)
  have hH₀ : 0 < H := zero_lt_one.trans_le hH
  have hz : 0 < z := by dsimp only [z]; linarith only [hs]
  have ha : 0 < a := Real.rpow_pos_of_pos (by positivity) _
  have haPow : a ^ z = c₀ / (4 * H) := by
    dsimp only [a]
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hz.ne', Real.rpow_one]
  refine ⟨a, ha, ?_⟩
  filter_upwards [eventually_regularBlockSize_bounds hH, eventually_ge_atTop (1 : ℕ)] with
    k hBlock hk
  intro n M hK hM
  have hk₀ : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hK' : (k : ℝ) ≤ a * (n : ℝ) ^ (1 / z) := by
    have he : 2 / (s + 3) = 1 / z := by
      dsimp only [z]
      field_simp [show s + 3 ≠ 0 by positivity]
    rwa [he] at hK
  have hp : (k : ℝ) ^ z ≤ c₀ / (4 * H) * (n : ℝ) := by
    refine (Real.rpow_le_rpow hk₀.le hK' hz.le).trans_eq ?_
    have hn : 0 ≤ (n : ℝ) ^ (1 / z) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    rw [Real.mul_rpow ha.le hn, haPow, ← Real.rpow_mul (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
      one_div_mul_cancel hz.ne', Real.rpow_one]
  have hM' : (n : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hM
  have hPow : 2 * H * (k : ℝ) ^ z ≤ c₀ * (M : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * H by positivity)
    have he : 2 * H * (c₀ / (4 * H) * (n : ℝ)) = c₀ * ((n : ℝ) / 2) := by
      field_simp [hH₀.ne'] <;> ring
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith only [hM']) hc.le)
  let u := (k : ℝ) ^ (s / 2)
  have hu : 0 < u := Real.rpow_pos_of_pos hk₀ _
  have hU : ((Real.sqrt k)⁻¹) ^ s = u⁻¹ := by
    dsimp only [u]
    rw [Real.inv_rpow (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul hk₀.le]
    congr 2
    ring
  have hZ : (k : ℝ) * Real.sqrt k * u = (k : ℝ) ^ z := by
    calc
      _ = (k : ℝ) ^ (1 : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ) * (k : ℝ) ^ (s / 2) := by
        rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
      _ = _ := by
        rw [← Real.rpow_add hk₀, ← Real.rpow_add hk₀]
        congr 1
        dsimp only [z]
        ring
  refine hBlock.2.2.1.trans ?_
  rw [hU, ← div_eq_mul_inv]
  apply (le_div_iff₀ hu).2
  rw [show 2 * H * (k : ℝ) * Real.sqrt k * u = 2 * H * ((k : ℝ) * Real.sqrt k * u) by ring, hZ]
  exact hPow

end BoundedEdgeRegularSubgraphs
