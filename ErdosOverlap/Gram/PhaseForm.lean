/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Gram.Covariance
public import ErdosOverlap.PhaseAlias

/-!
# Averaging exact quadratic forms over physical phase cells

This module transfers a concrete PSD theorem on the zero-sum subspace to the
actual phase covariance, and records its weighted first-moment constraint.
-/

@[expose] public section

namespace ErdosOverlap.Gram

open MeasureTheory Set
open scoped Interval BigOperators

noncomputable def tracePair {ι : Type*} [Fintype ι]
    (G X : ι → ι → ℝ) : ℝ := ∑ i, ∑ j, G i j * X i j

theorem form_cellAverage_continuous {h : ℝ → ℝ} (hh : Admissible h)
    {N : ℕ} (a : ℝ) (G : Fin (N+1) → Fin (N+1) → ℝ) :
    Continuous (fun s => form G (fun i => cellAverage h a s i.val)) := by
  unfold form
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  exact (continuous_const.mul (cellAverage_continuous hh a i.val)).mul
    (cellAverage_continuous hh a j.val)

theorem covariance_trace_identity {h : ℝ → ℝ} (hh : Admissible h)
    {N : ℕ} (a : ℝ) (G : Fin (N+1) → Fin (N+1) → ℝ) :
    (∫ s in (-a)..0, form G (fun i => cellAverage h a s i.val)) / a =
      tracePair G (fun i j => covariance h a i.val j.val) := by
  have hij (i j : Fin (N+1)) :
      IntervalIntegrable (fun s => G i j * cellAverage h a s i.val *
        cellAverage h a s j.val) volume (-a) 0 :=
    ((continuous_const.mul (cellAverage_continuous hh a i.val)).mul
      (cellAverage_continuous hh a j.val)).intervalIntegrable _ _
  have hi (i : Fin (N+1)) :
      IntervalIntegrable (fun s => ∑ j : Fin (N+1),
        G i j * cellAverage h a s i.val * cellAverage h a s j.val) volume (-a) 0 := by
    have hc : Continuous (fun s => ∑ j : Fin (N+1),
        G i j * cellAverage h a s i.val * cellAverage h a s j.val) := by
      apply continuous_finsetSum
      intro j hj
      exact (continuous_const.mul (cellAverage_continuous hh a i.val)).mul
        (cellAverage_continuous hh a j.val)
    exact hc.intervalIntegrable _ _
  unfold form tracePair
  rw [intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  simp_rw [intervalIntegral.integral_finsetSum (fun j _ => hij _ j)]
  simp only [mul_assoc, intervalIntegral.integral_const_mul, Finset.sum_div,
    covariance, mul_div_assoc]

/-- A concrete PSD matrix on zero-sum vectors has nonnegative pairing with
the actual physical covariance. -/
theorem covariance_trace_nonnegative {h : ℝ → ℝ} (hh : Admissible h)
    {N : ℕ} {a : ℝ} (ha : 0 < a) (hNa : (N : ℝ)*a = 2)
    (G : Fin (N+1) → Fin (N+1) → ℝ)
    (hG : ∀ y : Fin (N+1) → ℝ, (∑ i, y i) = 0 → 0 ≤ form G y) :
    0 ≤ tracePair G (fun i j => covariance h a i.val j.val) := by
  rw [← covariance_trace_identity hh a G]
  apply div_nonneg _ ha.le
  apply intervalIntegral.integral_nonneg (by linarith)
  intro s hs
  exact hG _ (sum_fin_cellAverage_eq_zero hh hNa hs)

theorem weighted_covariance_eq_meanSquare {h : ℝ → ℝ} (hh : Admissible h)
    {N : ℕ} (a : ℝ) :
    tracePair (fun i j : Fin (N+1) => (i.val : ℝ)*a*((j.val : ℝ)*a))
      (fun i j => covariance h a i.val j.val) =
      (∫ s in (-a)..0,
        (∑ i : Fin (N+1), (i.val : ℝ)*a*cellAverage h a s i.val)^2) / a := by
  rw [← covariance_trace_identity hh a]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  simp only [form, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The sharp alias estimate is now a constraint on the same covariance
matrix used by every exact Gram certificate. -/
theorem covariance_mean_bound {h : ℝ → ℝ} (hh : Admissible h)
    {N : ℕ} {a : ℝ} (ha : 0 < a) (hNa : (N : ℝ)*a = 2) :
    tracePair (fun i j : Fin (N+1) => (i.val : ℝ)*a*((j.val : ℝ)*a))
      (fun i j => covariance h a i.val j.val) ≤
      1/12 + (profileMean (overlapProfile h)/a)^2 := by
  rw [weighted_covariance_eq_meanSquare hh a]
  exact fin_weightedCells_meanSquare_le hh ha hNa

end ErdosOverlap.Gram
