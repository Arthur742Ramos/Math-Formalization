module

public import BoundedEdgeRegularSubgraphs.Model
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Tactic

/-!
# The almost-sure consequence of the amplified failure bound
-/

public section

open MeasureTheory Filter
open scoped ENNReal

namespace BoundedEdgeRegularSubgraphs

/-- For sufficiently large orders the amplified failure bound is dominated
by a summable reciprocal square. -/
theorem amplified_failure_le_inv_sq (n : ℕ) (hn : 256 ≤ n) :
    Real.exp (-Real.sqrt n * Real.log n / 8) ≤ ((n : ℝ) ^ 2)⁻¹ := by
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn' : (256 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hs : (16 : ℝ) ≤ Real.sqrt n :=
    (Real.le_sqrt (by norm_num) hn₀.le).mpr (by norm_num; exact hn)
  calc
    _ ≤ Real.exp (-(2 * Real.log n)) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_right hs hlog]
    _ = _ := by
      rw [Real.exp_neg]
      rw [show 2 * Real.log n = Real.log ((n : ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
        Real.exp_log (sq_pos_of_pos hn₀)]

/-- A coupling with the amplified marginal failure bound eventually satisfies
the order threshold almost surely, as in Corollary 7.2. -/
theorem ae_eventually_success_of_amplified_failure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (success : ℕ → Set Ω) (n₀ : ℕ)
    (h : ∀ n ≥ n₀, μ.real (success n)ᶜ ≤ Real.exp (-Real.sqrt n * Real.log n / 8)) :
    ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∈ success n := by
  let f (n : ℕ) := μ.real (success n)ᶜ
  let g (n : ℕ) := ((n : ℝ) ^ 2)⁻¹
  have hg : Summable g := Real.summable_nat_pow_inv.mpr (by norm_num)
  let N := max n₀ 256
  have htail (n : ℕ) : f (n + N) ≤ g (n + N) := by
    have hn₁ : n₀ ≤ n + N := (le_max_left _ _).trans (Nat.le_add_left _ _)
    have hn₂ : 256 ≤ n + N := (le_max_right _ _).trans (Nat.le_add_left _ _)
    exact (h _ hn₁).trans (amplified_failure_le_inv_sq _ hn₂)
  have hf : Summable f := (summable_nat_add_iff N).mp
    (Summable.of_nonneg_of_le (fun _ ↦ measureReal_nonneg) htail
      ((summable_nat_add_iff N).mpr hg))
  have hsum : (∑' n, μ (success n)ᶜ) ≠ ∞ := by
    have he (n : ℕ) : μ (success n)ᶜ = ENNReal.ofReal (f n) := (ofReal_measureReal (μ := μ) (s := (success n)ᶜ)).symm
    simp_rw [he]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ measureReal_nonneg) hf]
    exact ENNReal.ofReal_ne_top
  simpa using (ae_eventually_notMem (μ := μ) hsum)

end BoundedEdgeRegularSubgraphs
