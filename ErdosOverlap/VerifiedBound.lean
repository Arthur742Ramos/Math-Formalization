/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.FrontierConsequences

/-! # Fully instantiated continuous and discrete minimum-overlap lower bounds

This source has no numerical or analytic certificate hypotheses. Its native
and outer imports must all compile before the numerical conclusion is proved.
The discrete theorem concerns the original finite integer partitions, through
the exact cell embedding and interpolation theorem.
-/

@[expose] public section

namespace ErdosOverlap

theorem verified_peak_gt_auxiliary {h : ℝ → ℝ} (hh : Admissible h) :
    (380627990701/1000000000000 : ℝ) < overlapPeak h := frontier_peak_gt hh

theorem verified_auxiliary_le_relaxedOverlapConstant :
    (380627990701/1000000000000 : ℝ) ≤ relaxedOverlapConstant :=
  frontier_le_relaxedOverlapConstant

theorem verified_auxiliary_le_erdosOverlapConstant :
    (380627990701/1000000000000 : ℝ) ≤ erdosOverlapConstant :=
  verified_auxiliary_le_relaxedOverlapConstant.trans
    relaxedOverlapConstant_le_erdosOverlapConstant

theorem verified_auxiliary_le_discreteOverlapConstant :
    (380627990701/1000000000000 : ℝ) ≤ Discrete.discreteOverlapConstant :=
  verified_auxiliary_le_erdosOverlapConstant.trans
    Discrete.erdosOverlapConstant_le_discreteOverlapConstant

theorem verified_headline_lt_relaxedOverlapConstant :
    (3806279907/10000000000 : ℝ) < relaxedOverlapConstant :=
  (by norm_num : (3806279907/10000000000 : ℝ) < 380627990701/1000000000000).trans_le
    verified_auxiliary_le_relaxedOverlapConstant

theorem verified_headline_lt_erdosOverlapConstant :
    (3806279907/10000000000 : ℝ) < erdosOverlapConstant :=
  verified_headline_lt_relaxedOverlapConstant.trans_le
    relaxedOverlapConstant_le_erdosOverlapConstant

theorem verified_headline_lt_discreteOverlapConstant :
    (3806279907/10000000000 : ℝ) < Discrete.discreteOverlapConstant :=
  verified_headline_lt_erdosOverlapConstant.trans_le
    Discrete.erdosOverlapConstant_le_discreteOverlapConstant

theorem verified_auxiliary_lt_minimumOverlapQuotient {N : ℕ} (hN : 0 < N) :
    (380627990701/1000000000000 : ℝ) < Discrete.minimumOverlapQuotient N := by
  obtain ⟨A, B, hp, hv⟩ := Discrete.minimumOverlap_attained N
  have h := frontier_peak_gt
    (Discrete.density_admissible hN hp.left_subset hp.card_left)
  rw [Discrete.density_overlapPeak_eq hN hp, hv] at h
  exact h

/-- Literal Erdős36 conclusion for every positive size, with a strict count. -/
theorem verified_finite_partition_difference {N : ℕ} (hN : 0 < N)
    (A B : Finset ℤ) (hd : Disjoint A B)
    (hu : A ∪ B = Finset.Icc 1 (2*(N : ℤ))) (hcard : A.card = B.card) :
    ∃ k : ℤ, (3806279907/10000000000 : ℝ)*(N : ℝ) <
      (((A ×ˢ B).filter (fun p => p.1-p.2=k)).card : ℝ) :=
  Discrete.exists_difference_gt_of_lt_constant verified_headline_lt_erdosOverlapConstant hN
    (Discrete.balancedPartition_iff.mpr ⟨hd,hu,hcard⟩)

end ErdosOverlap
