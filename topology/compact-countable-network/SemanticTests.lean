module

import CNSolution

open Set Topology TopologicalSpace CountableNetwork

universe u v

-- Literal definition contract: network members have no openness requirement.
example {X : Type u} [TopologicalSpace X] (N : Set (Set X)) :
    IsNetwork N ↔ ∀ U, IsOpen U → ∀ x ∈ U, ∃ A ∈ N, x ∈ A ∧ A ⊆ U := Iff.rfl

private theorem singleton_network {X : Type u} [TopologicalSpace X] :
    IsNetwork (range (fun x : X => ({x} : Set X))) := by
  intro U _ x hx
  exact ⟨{x}, ⟨x, rfl⟩, mem_singleton x, singleton_subset_iff.mpr hx⟩

-- Even a non-Hausdorff countable space has a countable network.
private theorem countable_type_network (X : Type u) [TopologicalSpace X] [Countable X] :
    HasCountableNetwork X :=
  ⟨range (fun x : X => ({x} : Set X)), countable_range _, singleton_network⟩

-- An empty network works on the empty space; no nonempty enumeration is needed.
example [TopologicalSpace Empty] : IsNetwork (∅ : Set (Set Empty)) := by
  intro U _ x
  exact x.elim

example [TopologicalSpace Empty] : MetrizableSpace Empty :=
  metrizableSpace_of_countable_network countable_empty (by intro U _ x; exact x.elim)

-- Arbitrary universes and the exact metric topology are preserved.
example {X : Type u} (t : TopologicalSpace X) [CompactSpace X] [T2Space X]
    (h : HasCountableNetwork X) :
    ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t :=
  exists_compatibleMetric h

-- Subspaces need neither closedness nor compactness to inherit the network.
example (S : Set ℝ) : HasCountableNetwork S :=
  HasCountableNetwork.subtype hasCountableNetwork_of_secondCountable S

-- Compact-subspace metrization does not assume the ambient space compact,
-- normal, second countable, or metrizable.
example {X : Type u} [TopologicalSpace X] [T2Space X] (h : HasCountableNetwork X)
    (S : Set X) (hc : IsCompact S) : MetrizableSpace S :=
  metrizable_compact_subspace h hc

-- Continuous surjective network transport does not assume separation.
example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (h : HasCountableNetwork X) (f : X → Y) (hf : Continuous f)
    (hs : Function.Surjective f) : HasCountableNetwork Y :=
  h.of_continuous_surjective hf hs

section Indiscrete
local instance : TopologicalSpace Bool := ⊤

example : CompactSpace Bool := inferInstance

-- These singleton network elements are not open; treating a network as a base
-- would therefore fail this positive test.
example : HasCountableNetwork Bool := countable_type_network Bool

example : ¬ IsOpen ({false} : Set Bool) := by
  intro h
  rcases (TopologicalSpace.isOpen_top_iff _).mp h with he | hu
  · have : false ∈ (∅ : Set Bool) := he ▸ mem_singleton false
    exact this
  · have : true ∈ ({false} : Set Bool) := hu.symm ▸ mem_univ true
    exact Bool.false_ne_true this.symm

-- Dropping Hausdorff separation from the compact criterion is false.
example : ¬ MetrizableSpace Bool := by
  intro h
  let : MetrizableSpace Bool := h
  have : Subsingleton Bool := subsingleton_iff_indiscreteTopology.mpr inferInstance
  exact Bool.false_ne_true (Subsingleton.elim false true)

end Indiscrete
