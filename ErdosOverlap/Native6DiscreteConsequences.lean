/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.DiscreteProblem
public import ErdosOverlap.Native6BoundConsequences

/-! # The native certificate's consequences for the original integer problem

The proof inputs are the same actual integral receipts needed by the
continuous theorem. The discrete embedding itself, including exact affine
interpolation and the minimum/liminf transfer, is unconditional.
-/

@[expose] public section

namespace ErdosOverlap.Certificate.CoarseNative6

open Discrete

theorem auxiliaryHeight_le_discreteConstant_of_native_integrals_and_needed
    (bounds : NativeIntegralBounds)
    (outer : PhysicalMeanInequalities outerRowsNeedingIntegrals auxiliaryHeight) :
    (auxiliaryHeight : ℝ) ≤ discreteOverlapConstant :=
  (auxiliaryHeight_le_erdosConstant_of_native_integrals_and_needed bounds outer).trans
    erdosOverlapConstant_le_discreteOverlapConstant

theorem headline_lt_discreteConstant_of_native_integrals_and_needed
    (bounds : NativeIntegralBounds)
    (outer : PhysicalMeanInequalities outerRowsNeedingIntegrals auxiliaryHeight) :
    (headlineTarget : ℝ) < discreteOverlapConstant :=
  ((Rat.cast_lt (K := ℝ)).2 height_order.2.2.1).trans_le
    (auxiliaryHeight_le_discreteConstant_of_native_integrals_and_needed bounds outer)

theorem auxiliaryHeight_lt_minimumOverlapQuotient_of_native_integrals_and_needed
    (bounds : NativeIntegralBounds)
    (outer : PhysicalMeanInequalities outerRowsNeedingIntegrals auxiliaryHeight)
    {N : ℕ} (hN : 0 < N) :
    (auxiliaryHeight : ℝ) < minimumOverlapQuotient N := by
  obtain ⟨A,B,hp,hv⟩ := minimumOverlap_attained N
  have h := peak_gt_auxiliaryHeight_of_native_integrals_and_needed bounds outer
    (density_admissible hN hp.left_subset hp.card_left)
  rw [density_overlapPeak_eq hN hp, hv] at h
  exact h

/-- The literal integer representation-count conclusion, for every positive
`N`, follows from the actual native and outer integral certificates. -/
theorem headline_finite_partitions_of_native_integrals_and_needed
    (bounds : NativeIntegralBounds)
    (outer : PhysicalMeanInequalities outerRowsNeedingIntegrals auxiliaryHeight)
    {N : ℕ} (hN : 0 < N) (A B : Finset ℤ)
    (hd : Disjoint A B) (hu : A ∪ B = Finset.Icc 1 (2*(N : ℤ)))
    (hcard : A.card = B.card) :
    ∃ k : ℤ, (headlineTarget : ℝ)*(N : ℝ) <
      (((A ×ˢ B).filter (fun p => p.1-p.2=k)).card : ℝ) := by
  have hc : (headlineTarget : ℝ) < erdosOverlapConstant :=
    ((Rat.cast_lt (K := ℝ)).2 height_order.2.2.1).trans_le
      (auxiliaryHeight_le_erdosConstant_of_native_integrals_and_needed bounds outer)
  exact exists_difference_gt_of_lt_constant hc hN (balancedPartition_iff.mpr ⟨hd,hu,hcard⟩)

end ErdosOverlap.Certificate.CoarseNative6
