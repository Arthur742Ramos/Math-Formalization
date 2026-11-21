module

public import Statement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section
namespace InducedDegreeRepetition

open Filter

/-- Corollary 2 follows from Theorem 1, including its uniformity over host graphs. -/
theorem subexponential_of_logScale (main : LogScaleRepetition) : SubexponentialThreshold := by
  rw [SubexponentialThreshold, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨N₀, hmain⟩ := main (2 / ε) (by positivity) (1/2) (by norm_num) (by norm_num)
  rw [eventually_atTop]
  refine ⟨⌈(N₀ : ℝ) / ε⌉₊, ?_⟩
  intro k hk
  have hN : (N₀ : ℝ) ≤ ε * k := by
    have h := (Nat.le_ceil ((N₀ : ℝ) / ε)).trans (Nat.cast_le.mpr hk)
    linarith [(div_le_iff₀ hε).mp h]
  have hforce : Forces k ⌊Real.exp (ε * k)⌋₊ := by
    intro N hNbig G
    have hbig : Real.exp (ε * k) < N := (Nat.floor_lt' (by omega)).mp hNbig
    have hN₀ : N₀ ≤ N := by
      exact_mod_cast (show (N₀ : ℝ) ≤ N by linarith [Real.add_one_le_exp (ε * k)])
    obtain ⟨S, d, hlo, _, hrep⟩ := hmain N hN₀ G
    refine ⟨S, d, ?_⟩
    have hlog : ε * k < Real.log N := (Real.lt_log_iff_exp_lt ((Real.exp_pos _).trans hbig)).mpr hbig
    have hscale := (Nat.le_ceil ((2/ε) * Real.log N)).trans (Nat.cast_le.mpr hlo)
    have hr : 2 * (k : ℝ) ≤ (2 / ε) * Real.log N := by
      calc
        2 * (k : ℝ) = (2 / ε) * (ε * k) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hlog.le (by positivity)
    exact_mod_cast (show (k : ℝ) ≤ (degreeClass G S d).card by linarith)
  have hle : threshold k ≤ ⌊Real.exp (ε * k)⌋₊ := Nat.sInf_le hforce
  have hle' := (Nat.cast_le (α := ℝ)).mpr hle |>.trans (Nat.floor_le (Real.exp_pos _).le)
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  rcases Nat.eq_zero_or_pos (threshold k) with hzero | hpos
  · simp [hzero, (mul_nonneg hε.le (Nat.cast_nonneg k))]
  · rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hpos))]
    exact (Real.log_le_iff_le_exp (by exact_mod_cast hpos)).mpr hle'

end InducedDegreeRepetition
