/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.FrontierVerifiedBound
public import ErdosOverlap.DiscreteProblem

/-! The stronger continuous and discrete Erdős 36 bounds. -/

namespace ErdosOverlap
public section

theorem frontier_peak_gt {h : ℝ → ℝ} (hh : Admissible h) :
    (380627990701 / 1000000000000 : ℝ) < overlapPeak h := by
  simpa only [Certificate.FrontierCover.height, Rat.cast_div, Rat.cast_ofNat] using
    Certificate.FrontierCover.peak_gt_height hh

theorem frontier_le_relaxedOverlapConstant :
    (380627990701 / 1000000000000 : ℝ) ≤ relaxedOverlapConstant := by
  simpa only [Certificate.FrontierCover.height, Rat.cast_div, Rat.cast_ofNat] using
    Certificate.FrontierCover.height_le_relaxedConstant

theorem frontier_le_erdosOverlapConstant :
    (380627990701 / 1000000000000 : ℝ) ≤ erdosOverlapConstant :=
  frontier_le_relaxedOverlapConstant.trans relaxedOverlapConstant_le_erdosOverlapConstant

theorem frontier_le_discreteOverlapConstant :
    (380627990701 / 1000000000000 : ℝ) ≤ Discrete.discreteOverlapConstant :=
  frontier_le_erdosOverlapConstant.trans Discrete.erdosOverlapConstant_le_discreteOverlapConstant

theorem frontier_headline_lt_erdosOverlapConstant :
    (3806279907 / 10000000000 : ℝ) < erdosOverlapConstant :=
  (by norm_num : (3806279907 / 10000000000 : ℝ) < 380627990701 / 1000000000000).trans_le
    frontier_le_erdosOverlapConstant

theorem frontier_finite_partition_difference {N : ℕ} (hN : 0 < N)
    (A B : Finset ℤ) (hd : Disjoint A B)
    (hu : A ∪ B = Finset.Icc 1 (2 * (N : ℤ))) (hcard : A.card = B.card) :
    ∃ k : ℤ, (3806279907 / 10000000000 : ℝ) * (N : ℝ) <
      (((A ×ˢ B).filter (fun p => p.1 - p.2 = k)).card : ℝ) :=
  Discrete.exists_difference_gt_of_lt_constant frontier_headline_lt_erdosOverlapConstant hN
    (Discrete.balancedPartition_iff.mpr ⟨hd, hu, hcard⟩)

end
end ErdosOverlap
