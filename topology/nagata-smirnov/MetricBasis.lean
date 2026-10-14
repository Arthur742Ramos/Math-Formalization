/-
Copyright (c) 2026 Arthur Freitas Ramos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module

public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Bases

/-!
# Locally finite metric basis layers

Each metric ball cover at radius `1 / (n + 1)` has a locally finite open refinement.
The ranges of those refinements form an open basis. The index set of each layer
can have arbitrary cardinality: only the sequence of layers is countable.
-/

public section

open Set TopologicalSpace Metric

namespace NagataSmirnov

variable {X : Type*} [TopologicalSpace X]

/-- Every metrizable space admits an open basis that is a countable union of locally
finite families. No separability or countability of the individual layers is required. -/
theorem exists_sigmaLocallyFiniteBasis [MetrizableSpace X] :
    ∃ B : ℕ → Set (Set X),
      (∀ n, LocallyFinite (fun U : B n => (U : Set X))) ∧
        IsTopologicalBasis (⋃ n, B n) := by
  classical
  let : MetricSpace X := metrizableSpaceMetric X
  have hr : ∀ n : ℕ, 0 < 1 / (n + 1 : ℝ) := fun n =>
    div_pos zero_lt_one (Nat.cast_add_one_pos n)
  have hc : ∀ n : ℕ, ⋃ x : X, ball x (1 / (n + 1 : ℝ)) = univ := by
    intro n
    exact iUnion_eq_univ_iff.mpr fun x => ⟨x, mem_ball_self (hr n)⟩
  choose V hVo hVc hVf hVs using fun n : ℕ =>
    precise_refinement (fun x : X => ball x (1 / (n + 1 : ℝ)))
      (fun _ => isOpen_ball) (hc n)
  refine ⟨fun n => range (V n), fun n => (hVf n).on_range, ?_⟩
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro U hU
    rcases mem_iUnion.mp hU with ⟨n, x, rfl⟩
    exact hVo n x
  · intro x U hx hU
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
    obtain ⟨c, hxc⟩ := iUnion_eq_univ_iff.mp (hVc n) x
    refine ⟨V n c, mem_iUnion.mpr ⟨n, mem_range_self c⟩, hxc, ?_⟩
    intro y hy
    apply hεU
    have hyc := hVs n c hy
    have hxc' := hVs n c hxc
    rw [mem_ball] at hyc hxc' ⊢
    calc
      dist y x ≤ dist y c + dist c x := dist_triangle _ _ _
      _ = dist y c + dist x c := by rw [dist_comm c x]
      _ < 1 / (n + 1 : ℝ) + 1 / (n + 1 : ℝ) := add_lt_add hyc hxc'
      _ < ε := (add_lt_add hn hn).trans_eq (add_halves ε)

end NagataSmirnov
