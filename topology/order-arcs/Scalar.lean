/-
Copyright (c) 2026 Arthur Freitas Ramos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos
-/
module

public import Checkpoint
public import Mathlib.Analysis.Normed.Group.FunctionSeries

@[expose] public section

open Set Topology TopologicalSpace Metric

namespace OrderArcs

/-- A continuous scalar that increases strictly with inclusion. It is not
normalized on singleton sets. -/
noncomputable def height {X : Type*} [mX : MetricSpace X] (q : ℕ → X)
    (K : NonemptyCompacts X) : ℝ :=
  -∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * infDist (q n) (K : Set X)

theorem exists_infDist_bound {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ → X) : ∃ C : ℝ, ∀ n : ℕ, ∀ K : NonemptyCompacts X, infDist (q n) (K : Set X) ≤ C := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp (isCompact_univ (X := X)).isBounded
  refine ⟨C, fun n K => ?_⟩
  obtain ⟨z, hz⟩ := K.nonempty
  exact (infDist_le_dist_of_mem hz).trans (hC (mem_univ _) (mem_univ _))

private theorem summable_weight : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) :=
  summable_geometric_two.comp_injective Nat.succ_injective

private theorem weighted_bound {X : Type*} [MetricSpace X] (q : ℕ → X)
    {C : ℝ} (hC : ∀ n : ℕ, ∀ K : NonemptyCompacts X, infDist (q n) (K : Set X) ≤ C)
    (n : ℕ) (K : NonemptyCompacts X) :
    ‖(1 / 2 : ℝ) ^ (n + 1) * infDist (q n) (K : Set X)‖ ≤ (1 / 2 : ℝ) ^ (n + 1) * C := by
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) infDist_nonneg)]
  exact mul_le_mul_of_nonneg_left (hC n K) (by positivity)

theorem summable_weighted_infDist {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ → X) (K : NonemptyCompacts X) :
    Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * infDist (q n) (K : Set X)) := by
  obtain ⟨C, hC⟩ := exists_infDist_bound q
  exact (summable_weight.mul_right C).of_norm_bounded fun n => weighted_bound q hC n K

theorem continuous_height {X : Type*} [MetricSpace X] [CompactSpace X] (q : ℕ → X) :
    Continuous (height q) := by
  obtain ⟨C, hC⟩ := exists_infDist_bound q
  apply Continuous.neg
  exact continuous_tsum
    (fun n => (NonemptyCompacts.lipschitz_infDist_const (q n)).continuous.const_mul _)
    (summable_weight.mul_right C) (weighted_bound q hC)

theorem strictMono_height {X : Type*} [MetricSpace X] [CompactSpace X] (q : ℕ → X)
    (hq : DenseRange q) : StrictMono (height q) := by
  intro K L hKL
  obtain ⟨n, hn⟩ := exists_infDist_strict q hq hKL
  apply neg_lt_neg
  exact Summable.tsum_lt_tsum
    (fun m => mul_le_mul_of_nonneg_left
      (infDist_le_infDist_of_subset hKL.le K.nonempty) (by positivity))
    (mul_lt_mul_of_pos_left hn (by positivity))
    (summable_weighted_infDist q L) (summable_weighted_infDist q K)

end OrderArcs

#print axioms OrderArcs.continuous_height
#print axioms OrderArcs.strictMono_height
