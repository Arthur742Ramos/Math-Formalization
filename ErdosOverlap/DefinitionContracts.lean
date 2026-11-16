/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.DiscreteDensity

/-! Explicit logical contracts for the two structure predicates in the statement. -/

namespace ErdosOverlap
open MeasureTheory Set
open scoped Interval
public section

theorem admissible_fields {h : ℝ → ℝ} :
    Admissible h ↔ Measurable h ∧
      (∀ x ∈ Icc (0 : ℝ) 2, 0 ≤ h x) ∧
      (∀ x ∈ Icc (0 : ℝ) 2, h x ≤ 1) ∧
      (∫ x in (0 : ℝ)..2, h x) = 1 := by
  constructor
  · intro hh
    exact ⟨hh.measurable, hh.nonneg, hh.le_one, hh.mass⟩
  · rintro ⟨hm, hn, hl, hi⟩
    exact ⟨hm, hn, hl, hi⟩

namespace Discrete

theorem balancedPartition_fields {N : ℕ} {A B : Finset ℤ} :
    BalancedPartition N A B ↔ Disjoint A B ∧
      A ∪ B = Finset.Icc 1 (2*(N : ℤ)) ∧ A.card = N ∧ B.card = N := by
  constructor
  · intro hp
    exact ⟨hp.disjoint, hp.union, hp.card_left, hp.card_right⟩
  · rintro ⟨hd, hu, ha, hb⟩
    exact ⟨hd, hu, ha, hb⟩

end Discrete
end
end ErdosOverlap
