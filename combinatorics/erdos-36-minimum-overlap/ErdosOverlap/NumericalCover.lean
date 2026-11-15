/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Kernel-checked exact cover for the native6 lower-bound certificate

The exact finite statement is unconditional: for every real mean in `[-1,1]`,
one of 202 rational rows covering that mean has return strictly above
`0.3806279485`. This follows from kernel-checked rational inequalities and the
general concave-quadratic lemma, not from a sampled grid or Python's verdict.

The final lower-bound theorem is explicitly conditional on `AnalyticReturns`.
That hypothesis states the fixed-target inequalities for the generated rows;
it is an assembly interface, not a proof of the physical lower bound. On the
covered means it is in fact equivalent to exceeding the auxiliary height, as
`analyticReturns_iff_peak_gt` makes explicit. Deriving these inequalities for
physical overlap functions requires the analytic kernel/Gram inequalities and
the validity of the integral enclosures. Those obligations are not discharged
by reading the original Arb reports, their PASS fields, or their hashes.

No new axioms, `sorry`, `native_decide`, or external proof oracle are used.
-/

@[expose] public section

namespace ErdosOverlap.NumericalCover

open Certificate

/-- The exact numerical certificate separates every real mean in the full
interval. This theorem has no overlap-specific analytic hypotheses. -/
theorem exists_separating_row (m : ℝ) (hmlo : -1 ≤ m) (hmhi : m ≤ 1) :
    ∃ r ∈ Native6.allRows,
      (r.lo : ℝ) ≤ m ∧ m ≤ (r.hi : ℝ) ∧
      (Native6.auxiliaryHeight : ℝ) < r.eval m := by
  apply Certificate.exists_separating_row Native6.allRows_chain Native6.allRows_valid m
  · simpa using hmlo
  · simpa using hmhi

/-- The precise remaining analytic interface. Under the contradiction
hypothesis that the peak is at most the fixed auxiliary height, every
applicable row has return at most that height. No prior lower bound is used. -/
def AnalyticReturns (peak mean : ℝ) : Prop :=
  ∀ r ∈ Native6.allRows,
    (r.lo : ℝ) ≤ mean → mean ≤ (r.hi : ℝ) →
    peak ≤ (Native6.auxiliaryHeight : ℝ) →
    r.eval mean ≤ (Native6.auxiliaryHeight : ℝ)

/-- Combining the exact cover with the fixed-target analytic inequalities
excludes every peak at or below the auxiliary height. -/
theorem peak_gt_auxiliary (peak mean : ℝ) (hmlo : -1 ≤ mean) (hmhi : mean ≤ 1)
    (hreturns : AnalyticReturns peak mean) :
    (Native6.auxiliaryHeight : ℝ) < peak := by
  by_contra h
  have hcap : peak ≤ (Native6.auxiliaryHeight : ℝ) := le_of_not_gt h
  rcases exists_separating_row mean hmlo hmhi with ⟨r, hr, hlo, hhi, hsep⟩
  exact (not_lt_of_ge (hreturns r hr hlo hhi hcap)) hsep

/-- This explicit equivalence records the logical boundary of the assembly
interface. Supplying `AnalyticReturns` without deriving its physical analytic
premises would already supply the auxiliary peak bound. -/
theorem analyticReturns_iff_peak_gt (peak mean : ℝ)
    (hmlo : -1 ≤ mean) (hmhi : mean ≤ 1) :
    AnalyticReturns peak mean ↔ (Native6.auxiliaryHeight : ℝ) < peak := by
  constructor
  · exact peak_gt_auxiliary peak mean hmlo hmhi
  · intro hpeak r hr hlo hhi hcap
    exact False.elim ((not_le_of_gt hpeak) hcap)

/-- A strict lower bound for the infimum of any nonempty admissible family.
The gap between the auxiliary height and headline handles strictness without
assuming the infimum is attained. -/
theorem headline_lt_sInf (peaks : Set ℝ) (hne : peaks.Nonempty)
    (hreturns : ∀ peak ∈ peaks,
      ∃ mean : ℝ, -1 ≤ mean ∧ mean ≤ 1 ∧ AnalyticReturns peak mean) :
    (Native6.headlineTarget : ℝ) < sInf peaks := by
  have hfloor : (Native6.auxiliaryHeight : ℝ) ≤ sInf peaks := by
    apply le_csInf hne
    intro peak hp
    rcases hreturns peak hp with ⟨mean, hmlo, hmhi, hret⟩
    exact (peak_gt_auxiliary peak mean hmlo hmhi hret).le
  have hstrict : (Native6.headlineTarget : ℝ) < (Native6.auxiliaryHeight : ℝ) := by
    exact (Rat.cast_lt (K := ℝ)).2 Native6.height_order.2.2.1
  exact hstrict.trans_le hfloor

end ErdosOverlap.NumericalCover
