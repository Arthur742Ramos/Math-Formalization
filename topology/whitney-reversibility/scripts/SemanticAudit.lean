/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module
public import Solution
@[expose] public section
open Set Topology TopologicalSpace
namespace WhitneyReversibility
example {A : Type*} [TopologicalSpace A] (x : A) :
    ¬ IsDecomposable ({x} : Set A) := by
  rintro ⟨P, Q, _, hP, _, _, hPS, _, hp, _, _⟩
  exact hp (Set.eq_singleton_iff_unique_mem.mpr
    ⟨by obtain ⟨y, hy⟩ := hP.nonempty
        have he := Set.mem_singleton_iff.mp (hPS hy)
        exact he ▸ hy,
      fun y hy => Set.mem_singleton_iff.mp (hPS hy)⟩)

example {A : Type*} [TopologicalSpace A] (x : A) :
    IsHereditarilyDecomposable ({x} : Set A) := by
  intro K hK _ _ hnt
  obtain ⟨a, ha, b, hb, hab⟩ := hnt
  exact False.elim (hab ((Set.mem_singleton_iff.mp (hK ha)).trans
    (Set.mem_singleton_iff.mp (hK hb)).symm))

example {X : Type*} [MetricSpace X] [CompactSpace X] (σ : Continuum X → ℝ) :
    IsSizeMap σ ↔ Continuous σ ∧ (∀ x, σ (singleton x) = 0) ∧
      ∀ A B : Continuum X, A.val ≤ B.val → σ A ≤ σ B := Iff.rfl

example {X : Type*} [MetricSpace X] [CompactSpace X] (μ : Continuum X → ℝ) :
    IsWhitneyMap μ ↔ Continuous μ ∧ (∀ x, μ (singleton x) = 0) ∧
      ∀ A B : Continuum X, A.val < B.val → μ A < μ B := Iff.rfl

end WhitneyReversibility

#print axioms WhitneyReversibility.isCompact_relativeLevel
#print axioms WhitneyReversibility.isConnected_relativeLevel
#print axioms WhitneyReversibility.familyUnion_relativeLevel
#print axioms WhitneyReversibility.exists_indecomposable_covering_family
#print axioms WhitneyReversibility.sequential_strong_whitney_reversibility
#print axioms WhitneyReversibility.Continuum
#print axioms WhitneyReversibility.singleton
#print axioms WhitneyReversibility.whole
#print axioms WhitneyReversibility.IsWhitneyMap
#print axioms WhitneyReversibility.IsSizeMap
#print axioms WhitneyReversibility.relativeLevel
#print axioms WhitneyReversibility.familyUnion
#print axioms WhitneyReversibility.IsDecomposable
#print axioms WhitneyReversibility.IsHereditarilyDecomposable
#print axioms WhitneyReversibility.connected_square_level
#print axioms WhitneyReversibility.connected_relativeLevel_pair
#print axioms WhitneyReversibility.isConnected_anchored_relativeLevel
#print axioms WhitneyReversibility.exists_minimal_covering_family
#print axioms WhitneyReversibility.minimal_covering_family_indecomposable
