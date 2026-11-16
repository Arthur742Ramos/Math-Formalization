/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import Solution
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Lattice.Nat

namespace ErdosOverlap.MaterialAuditSolution
public section

open MeasureTheory Set
open scoped Interval

-- BEGIN material-imported-definition audit

theorem default_borel : (inferInstance : MeasurableSpace ℝ) = borel ℝ := rfl

theorem borel_generation : borel ℝ = MeasurableSpace.generateFrom {s : Set ℝ | IsOpen s} := rfl

theorem measurable_preimages (h : ℝ → ℝ) :
    Measurable h ↔ ∀ s : Set ℝ, MeasurableSet s → MeasurableSet (h ⁻¹' s) := Iff.rfl

theorem measurable_sets_generated (s : Set ℝ) :
    MeasurableSet s ↔ MeasurableSpace.GenerateMeasurable {u : Set ℝ | IsOpen u} s := Iff.rfl

theorem admissible_contract (h : ℝ → ℝ) :
    ErdosOverlap.Admissible h ↔ Measurable h ∧
      (∀ x ∈ Icc (0 : ℝ) 2, 0 ≤ h x) ∧
      (∀ x ∈ Icc (0 : ℝ) 2, h x ≤ 1) ∧
      (∫ x in (0 : ℝ)..2, h x) = 1 := ErdosOverlap.admissible_fields

theorem interval_orientation (f : ℝ → ℝ) (a b : ℝ) :
    (∫ x in a..b, f x) =
      (∫ x in Set.Ioc a b, f x) - ∫ x in Set.Ioc b a, f x := rfl

theorem integrability_predicate (f : ℝ → ℝ) (μ : Measure ℝ) :
    Integrable f μ ↔ AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ := Iff.rfl

theorem restricted_measure (μ : Measure ℝ) (s t : Set ℝ) (ht : MeasurableSet t) :
    μ.restrict s t = μ (t ∩ s) := Measure.restrict_apply ht

theorem integrable_branch (f : ℝ → ℝ) (hf : Integrable f volume) :
    (∫ x, f x) = L1.integral (hf.toL1 f) := MeasureTheory.integral_eq f hf

theorem nonintegrable_branch (f : ℝ → ℝ) (hf : ¬ Integrable f volume) :
    (∫ x, f x) = 0 := MeasureTheory.integral_undef hf

theorem default_volume_length (a b : ℝ) :
    volume (Set.Ioc a b) = ENNReal.ofReal (b-a) := Real.volume_Ioc

theorem default_volume_endpoint (a : ℝ) : volume ({a} : Set ℝ) = 0 := Real.volume_singleton

theorem closed_interval (a b x : ℝ) : x ∈ Set.Icc a b ↔ a ≤ x ∧ x ≤ b := Iff.rfl

theorem half_open_interval (a b x : ℝ) : x ∈ Set.Ioc a b ↔ a < x ∧ x ≤ b := Iff.rfl

theorem image_contract (f : ℝ → ℝ) (s : Set ℝ) (y : ℝ) :
    y ∈ f '' s ↔ ∃ x ∈ s, f x = y := Iff.rfl

theorem union_contract (s t : Set ℝ) (y : ℝ) : y ∈ s ∪ t ↔ y ∈ s ∨ y ∈ t := Iff.rfl

theorem real_supremum (s : Set ℝ) (hne : s.Nonempty) (hb : BddAbove s) :
    (∀ x ∈ s, x ≤ sSup s) ∧ (∀ y, (∀ x ∈ s, x ≤ y) → sSup s ≤ y) := by
  have hh := Real.isLUB_sSup hne hb
  exact ⟨fun _ hx => hh.1 hx, fun _ hy => hh.2 hy⟩

theorem real_infimum (s : Set ℝ) (hne : s.Nonempty) (hb : BddBelow s) :
    (∀ x ∈ s, sInf s ≤ x) ∧ (∀ y, (∀ x ∈ s, y ≤ x) → y ≤ sInf s) := by
  have hh := Real.isGLB_sInf hne hb
  exact ⟨fun _ hx => hh.1 hx, fun _ hy => hh.2 hy⟩

theorem integer_interval (a b x : ℤ) :
    x ∈ Finset.Icc a b ↔ a ≤ x ∧ x ≤ b := Finset.mem_Icc

theorem finite_union (A B : Finset ℤ) (x : ℤ) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B :=
  Finset.mem_union

theorem finite_disjoint (A B : Finset ℤ) :
    Disjoint A B ↔ ∀ x, x ∈ A → x ∉ B := Finset.disjoint_left

theorem balanced_contract (N : ℕ) (A B : Finset ℤ) :
    ErdosOverlap.Discrete.BalancedPartition N A B ↔ Disjoint A B ∧
      A ∪ B = Finset.Icc 1 (2*(N : ℤ)) ∧ A.card = N ∧ B.card = N :=
  ErdosOverlap.Discrete.balancedPartition_fields

theorem filtered_pairs (A B : Finset ℤ) (a b k : ℤ) :
    (a,b) ∈ (A ×ˢ B).filter (fun p => p.1-p.2=k) ↔ a ∈ A ∧ b ∈ B ∧ a-b=k := by
  simp only [Finset.mem_filter, Finset.mem_product, and_assoc]

theorem finite_cardinality (s : Finset (ℤ × ℤ)) : s.card = Multiset.card s.val := rfl

theorem finite_supremum (s : Finset (ℤ × ℤ)) (f : (ℤ × ℤ) → ℕ) :
    (∀ x ∈ s, f x ≤ s.sup f) ∧ (∀ y, (∀ x ∈ s, f x ≤ y) → s.sup f ≤ y) :=
  ⟨fun _ hx => Finset.le_sup hx, fun _ hy => Finset.sup_le hy⟩

theorem empty_supremum (f : (ℤ × ℤ) → ℕ) : (∅ : Finset (ℤ × ℤ)).sup f = 0 := rfl

theorem natural_minimum (s : Set ℕ) (hne : s.Nonempty) :
    sInf s ∈ s ∧ ∀ x ∈ s, sInf s ≤ x :=
  ⟨Nat.sInf_mem hne, fun _ hx => Nat.sInf_le hx⟩

theorem natural_empty_infimum : sInf (∅ : Set ℕ) = 0 := Nat.sInf_empty

theorem tail_liminf (u : ℕ → ℝ) :
    Filter.liminf u Filter.atTop = sSup {a | ∃ N : ℕ, ∀ n ≥ N, a ≤ u n} := by
  rw [Filter.liminf_eq]
  congr 1
  ext a
  exact Filter.eventually_atTop

theorem discrete_liminf_contract : ErdosOverlap.Discrete.discreteOverlapConstant =
    sSup {a | ∃ N : ℕ, ∀ n ≥ N, a ≤ ErdosOverlap.Discrete.minimumOverlapQuotient n} :=
  tail_liminf _

-- END material-imported-definition audit

end
end ErdosOverlap.MaterialAuditSolution
