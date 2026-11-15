/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.LiminfLimsup

/-!
# Numerical lower bounds for Erdős' minimum-overlap problem

This independent statement surface uses only canonical Mathlib imports. The
theorem holes specify the intended results for Comparator; they are not proof
implementations. `NumericSolution` supplies the corresponding proofs without
importing this module. The numerical proof build is pending until every actual
native and outer integral certificate and the final solution module compile.

The continuous model has two complementary colours of mass one on an interval
of length two. Measurability here is Borel measurability. The two overlap
integrals represent all signed shifts; their supremum is the physical peak.
The relaxed and binary infima are distinguished explicitly.

The discrete model is the original problem: partition the first `2N` positive
integers into two `N`-element sets and count representations of `k=a-b`. The
maximum is taken over realized differences, and hence over all integer
differences. The infimum over finite partitions is a genuine attained natural
minimum. The normalized liminf gives the asymptotic lower-bound statement.

The stronger auxiliary value `0.3806279485` is a non-strict infimum/liminf lower
bound. Its strict gap above `0.380627948` supplies the headline. The finite
representation-count conclusion holds for every positive `N`, stronger than
the sufficiently-large-size quantifier in the public problem. The exact
optimal constant is not determined.
-/

@[expose] public section

namespace ErdosOverlap

open MeasureTheory Set
open scoped Interval

/-- A Borel measurable relaxed equal-mass partition on `[0,2]`. -/
structure Admissible (h : ℝ → ℝ) : Prop where
  measurable : Measurable h
  nonneg : ∀ x ∈ Icc (0 : ℝ) 2, 0 ≤ h x
  le_one : ∀ x ∈ Icc (0 : ℝ) 2, h x ≤ 1
  mass : (∫ x in (0 : ℝ)..2, h x) = 1

/-- Overlap at a nonnegative shift in `[0,2]`. -/
noncomputable def positiveOverlap (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..(2-t), h x * (1-h (x+t))

/-- Overlap at the negative of a nonnegative shift in `[0,2]`. -/
noncomputable def negativeOverlap (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..(2-t), h (x+t) * (1-h x)

noncomputable section

/-- The values of both signed overlaps on their entire physical interval. -/
def overlapValues (h : ℝ → ℝ) : Set ℝ :=
  positiveOverlap h '' Icc (0 : ℝ) 2 ∪ negativeOverlap h '' Icc (0 : ℝ) 2

/-- The supremum of the actual signed overlap values. -/
def overlapPeak (h : ℝ → ℝ) : ℝ := sSup (overlapValues h)

/-- All peaks of Borel measurable relaxed equal-mass partitions. -/
def relaxedPeaks : Set ℝ := {M | ∃ h : ℝ → ℝ, Admissible h ∧ overlapPeak h = M}

/-- The infimum over the relaxed continuous partition family. -/
def relaxedOverlapConstant : ℝ := sInf relaxedPeaks

/-- The binary subclass of the admissible continuous densities. -/
def BinaryAdmissible (h : ℝ → ℝ) : Prop :=
  Admissible h ∧ ∀ x ∈ Icc (0 : ℝ) 2, h x = 0 ∨ h x = 1

/-- All peaks of binary measurable equal-mass partitions. -/
def partitionPeaks : Set ℝ :=
  {M | ∃ h : ℝ → ℝ, BinaryAdmissible h ∧ overlapPeak h = M}

/-- The continuous binary minimum-overlap infimum. -/
def erdosOverlapConstant : ℝ := sInf partitionPeaks

namespace Discrete

/-- The number of integer pairs in `A × B` with difference `a-b=k`. -/
def differenceCount (A B : Finset ℤ) (k : ℤ) : ℕ :=
  ((A ×ˢ B).filter (fun p => p.1-p.2=k)).card

/-- The greatest difference count, using all realized integer differences. -/
def maximumCount (A B : Finset ℤ) : ℕ :=
  (A ×ˢ B).sup (fun p => differenceCount A B (p.1-p.2))

/-- A disjoint full partition of `{1,…,2N}` into two `N`-element sets. -/
structure BalancedPartition (N : ℕ) (A B : Finset ℤ) : Prop where
  disjoint : Disjoint A B
  union : A ∪ B = Finset.Icc 1 (2*(N : ℤ))
  card_left : A.card = N
  card_right : B.card = N

/-- The possible maximum counts among all balanced partitions of size `2N`. -/
def finiteMaximumValues (N : ℕ) : Set ℕ :=
  {z | ∃ A B : Finset ℤ, BalancedPartition N A B ∧ maximumCount A B = z}

/-- The minimum possible largest integer difference count. -/
def minimumOverlap (N : ℕ) : ℕ := sInf (finiteMaximumValues N)

/-- The original finite minimum divided by the cardinality of one colour. -/
def minimumOverlapQuotient (N : ℕ) : ℝ := (minimumOverlap N : ℝ)/(N : ℝ)

/-- The asymptotic discrete minimum-overlap constant, stated as a liminf. -/
def discreteOverlapConstant : ℝ := Filter.liminf minimumOverlapQuotient Filter.atTop

end Discrete

/-- Every actual relaxed peak strictly exceeds the auxiliary height. -/
theorem verified_peak_gt_auxiliary {h : ℝ → ℝ} (hh : Admissible h) :
    (3806279485/10000000000 : ℝ) < overlapPeak h := by
  sorry

/-- Non-strict lower bound on the continuous relaxed infimum. -/
theorem verified_auxiliary_le_relaxedOverlapConstant :
    (3806279485/10000000000 : ℝ) ≤ relaxedOverlapConstant := by
  sorry

/-- Non-strict lower bound on the continuous binary infimum. -/
theorem verified_auxiliary_le_erdosOverlapConstant :
    (3806279485/10000000000 : ℝ) ≤ erdosOverlapConstant := by
  sorry

/-- The stronger lower bound for the original discrete normalized liminf. -/
theorem verified_auxiliary_le_discreteOverlapConstant :
    (3806279485/10000000000 : ℝ) ≤ Discrete.discreteOverlapConstant := by
  sorry

/-- The strict headline bound for the relaxed continuous infimum. -/
theorem verified_headline_lt_relaxedOverlapConstant :
    (380627948/1000000000 : ℝ) < relaxedOverlapConstant := by
  sorry

/-- The strict headline bound for the binary continuous infimum. -/
theorem verified_headline_lt_erdosOverlapConstant :
    (380627948/1000000000 : ℝ) < erdosOverlapConstant := by
  sorry

/-- The strict headline bound for the original discrete normalized liminf. -/
theorem verified_headline_lt_discreteOverlapConstant :
    (380627948/1000000000 : ℝ) < Discrete.discreteOverlapConstant := by
  sorry

/-- Every positive-size finite minimum strictly exceeds the auxiliary level. -/
theorem verified_auxiliary_lt_minimumOverlapQuotient {N : ℕ} (hN : 0 < N) :
    (3806279485/10000000000 : ℝ) < Discrete.minimumOverlapQuotient N := by
  sorry

/-- The literal integer representation-count conclusion for every `N>0`. -/
theorem verified_finite_partition_difference {N : ℕ} (hN : 0 < N)
    (A B : Finset ℤ) (hd : Disjoint A B)
    (hu : A ∪ B = Finset.Icc 1 (2*(N : ℤ))) (hcard : A.card = B.card) :
    ∃ k : ℤ, (380627948/1000000000 : ℝ)*(N : ℝ) <
      (((A ×ˢ B).filter (fun p => p.1-p.2=k)).card : ℝ) := by
  sorry

end
end ErdosOverlap
