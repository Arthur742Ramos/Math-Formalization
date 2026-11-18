module

public import BoundedEdgeRegularSubgraphs.Tilt
import BoundedEdgeRegularSubgraphs.MeanDrift
import Mathlib.Tactic

/-!
# The optimized likelihood penalty in Proposition 8.1
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

omit [LinearOrder α] in
/-- The explicit tilt obtained by resolving the drift into its mean and centred parts. -/
noncomputable def varianceTilt (μ : α → ℝ) (d : ℝ) (i : α) : ℝ :=
  -(4 / (Fintype.card α - 2 : ℝ)) * (μ i - vertexMean μ) +
    (2 / (Fintype.card α - 1 : ℝ)) * (d - vertexMean μ)

/-- Evaluation of the quadratic bound at the optimizing tilt. -/
theorem varianceTilt_cost (μ : α → ℝ) (d : ℝ) (hn : 3 ≤ Fintype.card α) :
    (∑ i, varianceTilt μ d i * μ i) +
      (∑ e : Edge α, (varianceTilt μ d e.val.1 + varianceTilt μ d e.val.2) ^ 2) / 8 -
      (∑ i, varianceTilt μ d i * d) =
    -2 * (∑ i, (μ i - vertexMean μ) ^ 2) / (Fintype.card α - 2 : ℝ) -
      Fintype.card α * (d - vertexMean μ) ^ 2 / (Fintype.card α - 1 : ℝ) := by
  let n : ℝ := Fintype.card α
  let v (i : α) := μ i - vertexMean μ
  let w := d - vertexMean μ
  let a : ℝ := 4 / (n - 2)
  let b : ℝ := 2 / (n - 1) * w
  let t (i : α) := varianceTilt μ d i
  have ht (i : α) : t i = -a * v i + b := rfl
  have hv : ∑ i, v i = 0 := sum_sub_vertexMean μ
  have hlin : (∑ i, t i * (μ i - d)) =
      -a * (∑ i, v i ^ 2) - n * b * w := by
    calc
      _ = ∑ i, (-a * v i ^ 2 + (a * w + b) * v i - (b * w)) := by
        refine Finset.sum_congr rfl (fun i _ ↦ ?_)
        have hdiff : μ i - d = v i - w := by dsimp [v, w]; ring
        rw [ht, hdiff]
        ring
      _ = _ := by
        simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hv, nsmul_eq_mul, n]
        ring
  have hsum : (∑ i, t i) = n * b := by
    simp [ht, Finset.sum_add_distrib, ← Finset.mul_sum, hv, nsmul_eq_mul, n]
  have hsq : (∑ i, t i ^ 2) = a ^ 2 * (∑ i, v i ^ 2) + n * b ^ 2 := by
    calc
      _ = ∑ i, (a ^ 2 * v i ^ 2 - (2 * a * b) * v i + b ^ 2) := by
        refine Finset.sum_congr rfl (fun i _ ↦ ?_)
        rw [ht]
        ring
      _ = _ := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hv, nsmul_eq_mul, n]
  have hlin' : (∑ i, t i * μ i) - (∑ i, t i * d) =
      -a * (∑ i, v i ^ 2) - n * b * w := by
    simpa only [mul_sub, Finset.sum_sub_distrib] using hlin
  have hn' : (3 : ℝ) ≤ n := by
    dsimp [n]
    exact_mod_cast hn
  have hn₁ : n - 1 ≠ 0 := by linarith
  have hn₂ : n - 2 ≠ 0 := by linarith
  change (∑ i, t i * μ i) + (∑ e : Edge α, (t e.val.1 + t e.val.2) ^ 2) / 8 -
    (∑ i, t i * d) = -2 * (∑ i, v i ^ 2) / (n - 2) - n * w ^ 2 / (n - 1)
  rw [add_sub_right_comm, hlin', sum_edge_squares t, hsq, hsum]
  change -a * (∑ i, v i ^ 2) - n * b * w +
    ((n - 2) * (a ^ 2 * (∑ i, v i ^ 2) + n * b ^ 2) + (n * b) ^ 2) / 8 =
    -2 * (∑ i, v i ^ 2) / (n - 2) - n * w ^ 2 / (n - 1)
  dsimp only [a, b]
  field_simp [hn₁, hn₂]
  ring

/-- The exact variation penalty multiplying the centred-law degree atom. -/
theorem probability_regular_degree_atom_le_variance_tilt
    (p : Edge α → Set.Icc (0 : ℝ) 1) (d : ℤ) (hn : 3 ≤ Fintype.card α) :
    (graphLaw p).real (degreeAtom Finset.univ (fun _ ↦ d)) ≤
      Real.exp (-2 * degreeVariation p / (Fintype.card α - 2 : ℝ) -
        Fintype.card α * ((d : ℝ) - vertexMean (degreeSum fun e ↦ (p e : ℝ))) ^ 2 /
          (Fintype.card α - 1 : ℝ)) *
        (graphLaw (vertexTilt p (varianceTilt (degreeSum fun e ↦ (p e : ℝ)) d))).real
          (degreeAtom Finset.univ (fun _ ↦ d)) := by
  let μ := degreeSum fun e ↦ (p e : ℝ)
  have h := degreeAtom_original_le_tilted_cost p (varianceTilt μ d) (fun _ ↦ d)
  rw [varianceTilt_cost μ d hn] at h
  exact h

end BoundedEdgeRegularSubgraphs
