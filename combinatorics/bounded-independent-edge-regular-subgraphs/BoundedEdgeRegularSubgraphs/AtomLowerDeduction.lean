module

public import BoundedEdgeRegularSubgraphs.TiltEntropy
import Mathlib.Tactic

/-!
# Exponential lower bounds from the centred atom estimate
-/

public section

open MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- The lower-bound scale in Theorem B.2 follows from the determinant bound
and a positive constant multiplying the Gaussian normalization. -/
theorem exp_le_gaussian_atom_normalizer {n : ℕ} (hn : 1 ≤ n) {D c : ℝ}
    (hD : 0 < D) (hc : 0 < c) (hdet : D ≤ ((n : ℝ) / 2) ^ n) :
    Real.exp (-(n : ℝ) / 2 * Real.log n -
      (Real.log Real.pi / 2 + |Real.log c|) * n) ≤
        c / ((Real.sqrt (2 * Real.pi)) ^ n * Real.sqrt D) := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdetlog := Real.log_le_log hD hdet
  rw [Real.log_pow, Real.log_div hn₀.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hdetlog
  have hp : 0 < 2 * Real.pi := by positivity
  have hlog :
      Real.log (c / ((Real.sqrt (2 * Real.pi)) ^ n * Real.sqrt D)) =
        Real.log c - ((n : ℝ) * (Real.log 2 + Real.log Real.pi) / 2 + Real.log D / 2) := by
    rw [Real.log_div hc.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_sqrt hp.le, Real.log_sqrt hD.le,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_pos.ne']
    ring
  have h := neg_abs_le (Real.log c)
  have hh := mul_le_mul_of_nonneg_left hn₁ (abs_nonneg (Real.log c))
  rw [mul_one] at hh
  have hlogLower :
      -(n : ℝ) / 2 * Real.log n - (Real.log Real.pi / 2 + |Real.log c|) * n ≤
        Real.log (c / ((Real.sqrt (2 * Real.pi)) ^ n * Real.sqrt D)) := by
    rw [hlog]
    linarith only [hdetlog, h, hh]
  have he := Real.exp_le_exp.mpr hlogLower
  rwa [Real.exp_log (by positivity)] at he

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The lower-bound deduction of Lemma 2.1 from the corresponding bound
under the tilt. -/
theorem probability_degreeAtom_ge_of_centered_tilt_bound
    (q : Edge α → Set.Icc (0 : ℝ) 1) (θ : α → ℝ) (d : α → ℤ)
    (hmean : degreeSum (fun e ↦ (vertexTilt q θ e : ℝ)) = fun i ↦ (d i : ℝ))
    {B : ℝ} (hprob : Real.exp (-B) ≤
      (graphLaw (vertexTilt q θ)).real (degreeAtom Finset.univ d)) :
    Real.exp (-B - ((Fintype.card α - 1 : ℝ) / 4) * ∑ i, θ i ^ 2) ≤
      (graphLaw q).real (degreeAtom Finset.univ d) := by
  let K := (∑ i, θ i * (d i : ℝ)) - logPartition q θ
  have hK := (centered_vertexTilt_logLikelihood_bounds q θ (fun i ↦ (d i : ℝ)) hmean).2
  let C := ((Fintype.card α - 1 : ℝ) / 4) * ∑ i, θ i ^ 2
  have hK' : K ≤ C := hK
  have hlaw := real_graphLaw_vertexTilt_degreeAtom q θ d
  change _ = Real.exp K * (graphLaw q).real (degreeAtom Finset.univ d) at hlaw
  change Real.exp (-B - C) ≤ _
  calc
    _ ≤ Real.exp (-B - K) := Real.exp_le_exp.mpr (sub_le_sub_left hK' _)
    _ = Real.exp (-K) * Real.exp (-B) := by rw [sub_eq_add_neg, Real.exp_add, mul_comm]
    _ ≤ Real.exp (-K) * (graphLaw (vertexTilt q θ)).real (degreeAtom Finset.univ d) :=
      mul_le_mul_of_nonneg_left hprob (Real.exp_nonneg _)
    _ = _ := by rw [hlaw, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

end BoundedEdgeRegularSubgraphs
