module

import SDSolution

open Set Filter TopologicalSpace Sneider
open scoped Topology

universe u

-- The main contract is universe-polymorphic and assumes no countability or
-- nonemptiness of the underlying compact Hausdorff space.
example {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    MetrizableSpace X ↔ IsGδ (diagonal X) := metrizable_iff_isGdelta_diagonal

-- The metric's induced topology is the original one, not a finer/coarser topology.
example {X : Type u} [t : TopologicalSpace X] [CompactSpace X] [T2Space X]
    (h : IsGδ (diagonal X)) :
    ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t :=
  exists_compatibleMetric h

-- The general compact-normal bridge covers both empty and full closed sets.
example {X : Type u} [TopologicalSpace X] [CompactSpace X] [NormalSpace X] :
    (𝓝ˢ (∅ : Set X)).IsCountablyGenerated :=
  nhdsSet_isCountablyGenerated_of_isGδ isClosed_empty .empty

example {X : Type u} [TopologicalSpace X] [CompactSpace X] [NormalSpace X] :
    (𝓝ˢ (univ : Set X)).IsCountablyGenerated :=
  nhdsSet_isCountablyGenerated_of_isGδ isClosed_univ .univ

-- The empty finite intersection in the returned basis is exactly the universe.
example {X : Type u} (V : ℕ → Set X) :
    (⋂ n ∈ (∅ : Finset ℕ), V n) = univ := by simp

-- Necessity does not assume compactness (the real line is one instance).
example : IsGδ (diagonal ℝ) := isGdelta_diagonal

-- Empty spaces are included even when their topology is supplied arbitrarily.
example [TopologicalSpace Empty] : MetrizableSpace Empty := by
  apply metrizableSpace_of_isGdelta_diagonal
  have h : diagonal Empty = (∅ : Set (Empty × Empty)) := by
    ext p
    exact p.1.elim
  rw [h]
  exact .empty

section Indiscrete
local instance : TopologicalSpace Bool := ⊤

-- Compactness itself supplies no Gδ-diagonal premise on a non-Hausdorff space.
example : CompactSpace Bool := inferInstance

example : ¬ IsGδ (diagonal Bool) := by
  intro h
  obtain ⟨U, hU, hD⟩ := h.eq_iInter_nat
  have hsub (n : ℕ) : diagonal Bool ⊆ U n := by
    rw [hD]
    exact iInter_subset U n
  have hprod : (inferInstance : TopologicalSpace (Bool × Bool)) = ⊤ := by
    change TopologicalSpace.induced Prod.fst (⊤ : TopologicalSpace Bool) ⊓
      TopologicalSpace.induced Prod.snd (⊤ : TopologicalSpace Bool) = ⊤
    simp [induced_top]
  have hUn (n : ℕ) : U n = univ := by
    have hUn_open : @IsOpen (Bool × Bool) ⊤ (U n) := by
      rw [← hprod]
      exact hU n
    rcases (TopologicalSpace.isOpen_top_iff (U n)).mp hUn_open with hempty | huniv
    · have hp := hsub n (mem_diagonal false)
      simp [hempty] at hp
    · exact huniv
  have hp : (false, true) ∈ diagonal Bool := by
    rw [hD]
    exact mem_iInter.mpr fun n => by simp [hUn n]
  exact Bool.false_ne_true hp

end Indiscrete
