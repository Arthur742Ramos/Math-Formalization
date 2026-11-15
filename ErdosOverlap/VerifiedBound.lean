/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Native6VerifiedIntegrals
public import ErdosOverlap.Certificate.OuterPhysical
public import ErdosOverlap.Native6DiscreteConsequences

/-! # Fully instantiated continuous and discrete minimum-overlap lower bounds

This source has no numerical or analytic certificate hypotheses. Its native
and outer imports must all compile before the numerical conclusion is proved.
The discrete theorem concerns the original finite integer partitions, through
the exact cell embedding and interpolation theorem.
-/

@[expose] public section

namespace ErdosOverlap

open Certificate.CoarseNative6

theorem verified_peak_gt_auxiliary {h : ℝ → ℝ} (hh : Admissible h) :
    (3806279485/10000000000 : ℝ) < overlapPeak h := by
  have hbound := peak_gt_auxiliaryHeight_of_native_integrals_and_needed
    nativeIntegralBounds_verified outerRowsNeedingIntegrals_physical hh
  convert hbound using 1 <;> norm_num [auxiliaryHeight]

theorem verified_auxiliary_le_relaxedOverlapConstant :
    (3806279485/10000000000 : ℝ) ≤ relaxedOverlapConstant := by
  have hbound := auxiliaryHeight_le_relaxedConstant_of_native_integrals_and_needed
    nativeIntegralBounds_verified outerRowsNeedingIntegrals_physical
  convert hbound using 1 <;> norm_num [auxiliaryHeight]

theorem verified_auxiliary_le_erdosOverlapConstant :
    (3806279485/10000000000 : ℝ) ≤ erdosOverlapConstant :=
  verified_auxiliary_le_relaxedOverlapConstant.trans
    relaxedOverlapConstant_le_erdosOverlapConstant

theorem verified_auxiliary_le_discreteOverlapConstant :
    (3806279485/10000000000 : ℝ) ≤ Discrete.discreteOverlapConstant :=
  verified_auxiliary_le_erdosOverlapConstant.trans
    Discrete.erdosOverlapConstant_le_discreteOverlapConstant

theorem verified_headline_lt_relaxedOverlapConstant :
    (380627948/1000000000 : ℝ) < relaxedOverlapConstant :=
  (by norm_num : (380627948/1000000000 : ℝ) < 3806279485/10000000000).trans_le
    verified_auxiliary_le_relaxedOverlapConstant

theorem verified_headline_lt_erdosOverlapConstant :
    (380627948/1000000000 : ℝ) < erdosOverlapConstant :=
  verified_headline_lt_relaxedOverlapConstant.trans_le
    relaxedOverlapConstant_le_erdosOverlapConstant

theorem verified_headline_lt_discreteOverlapConstant :
    (380627948/1000000000 : ℝ) < Discrete.discreteOverlapConstant :=
  verified_headline_lt_erdosOverlapConstant.trans_le
    Discrete.erdosOverlapConstant_le_discreteOverlapConstant

theorem verified_auxiliary_lt_minimumOverlapQuotient {N : ℕ} (hN : 0 < N) :
    (3806279485/10000000000 : ℝ) < Discrete.minimumOverlapQuotient N := by
  have hbound := auxiliaryHeight_lt_minimumOverlapQuotient_of_native_integrals_and_needed
    nativeIntegralBounds_verified outerRowsNeedingIntegrals_physical hN
  convert hbound using 1 <;> norm_num [auxiliaryHeight]

/-- Literal Erdős36 conclusion for every positive size, with a strict count. -/
theorem verified_finite_partition_difference {N : ℕ} (hN : 0 < N)
    (A B : Finset ℤ) (hd : Disjoint A B)
    (hu : A ∪ B = Finset.Icc 1 (2*(N : ℤ))) (hcard : A.card = B.card) :
    ∃ k : ℤ, (380627948/1000000000 : ℝ)*(N : ℝ) <
      (((A ×ˢ B).filter (fun p => p.1-p.2=k)).card : ℝ) :=
  Discrete.exists_difference_gt_of_lt_constant verified_headline_lt_erdosOverlapConstant hN
    (Discrete.balancedPartition_iff.mpr ⟨hd,hu,hcard⟩)

end ErdosOverlap
