module

public import BoundedEdgeRegularSubgraphs.CenteredFourierExpansion
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Uniform smallness of the local Taylor remainder
-/

public section

open Filter
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- The radius used for the local box in Appendix A. -/
noncomputable def fourierBoxRadius (n : ℕ) : ℝ := Real.log n / Real.sqrt n

theorem fourierBoxRadius_tendsto_zero :
    Tendsto fourierBoxRadius atTop (nhds 0) := by
  have h := (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  change Tendsto (fun n : ℕ ↦ Real.log n / (n : ℝ) ^ (1 / 2 : ℝ)) atTop (nhds 0) at h
  unfold fourierBoxRadius
  simpa only [Real.sqrt_eq_rpow] using h

/-- The uniform upper bound on the sum of fifth powers tends to zero at the
radius (n^{-1/2}log n). -/
theorem fourierBox_fifth_error_tendsto_zero :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * (2 * fourierBoxRadius n) ^ 5) atTop (nhds 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : ℝ)) 5 (by norm_num)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  have hs : Tendsto (fun n : ℕ ↦ (Real.log n) ^ 5 / Real.sqrt n) atTop (nhds 0) := by
    change Tendsto (fun n : ℕ ↦ (Real.log n) ^ (5 : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ)) atTop (nhds 0) at h
    simpa only [Real.sqrt_eq_rpow, ← Real.rpow_natCast, Nat.cast_ofNat] using h
  have h32 : Tendsto (fun n : ℕ ↦ (32 : ℝ) * ((Real.log n) ^ 5 / Real.sqrt n)) atTop (nhds 0) :=
    by simpa only [mul_zero] using (tendsto_const_nhds (x := (32 : ℝ))).mul hs
  apply h32.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hsq := Real.sq_sqrt hn₀.le
  have hs5 : (Real.sqrt (n : ℝ)) ^ 5 = (n : ℝ) ^ 2 * Real.sqrt n := by
    calc
      _ = ((Real.sqrt (n : ℝ)) ^ 2) ^ 2 * Real.sqrt n := by ring
      _ = _ := by rw [hsq]
  rw [show 2 * fourierBoxRadius n = (2 * Real.log n) / Real.sqrt n by
    unfold fourierBoxRadius
    rw [mul_div_assoc], div_pow, hs5, mul_pow]
  field_simp [hn₀.ne', (Real.sqrt_pos.mpr hn₀).ne']
  ring

/-- The fifth-power sum on the full array is bounded uniformly over the local box. -/
theorem sum_edge_fifth_le_fourierBox (n : ℕ) (t : Fin n → ℝ)
    (ht : ∀ i, |t i| ≤ fourierBoxRadius n) :
    (∑ e : Edge (Fin n), |t e.val.1 + t e.val.2| ^ 5) ≤
      (n : ℝ) ^ 2 * (2 * fourierBoxRadius n) ^ 5 := by
  have hr : 0 ≤ fourierBoxRadius n :=
    div_nonneg (by cases n <;> simp [Real.log_nonneg]) (Real.sqrt_nonneg _)
  have hcard : (Fintype.card (Edge (Fin n)) : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h := Fintype.card_le_of_injective (fun e : Edge (Fin n) ↦ e.val) Subtype.val_injective
    rw [Fintype.card_prod, Fintype.card_fin, ← pow_two] at h
    exact_mod_cast h
  calc
    _ ≤ ∑ _ : Edge (Fin n), (2 * fourierBoxRadius n) ^ 5 := by
      apply Finset.sum_le_sum
      intro e _
      apply pow_le_pow_left₀ (abs_nonneg _)
      exact (abs_add_le _ _).trans (by linarith [ht e.val.1, ht e.val.2])
    _ = (Fintype.card (Edge (Fin n)) : ℝ) * (2 * fourierBoxRadius n) ^ 5 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

end BoundedEdgeRegularSubgraphs
