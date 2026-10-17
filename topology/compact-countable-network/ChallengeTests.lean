module

import CNChallenge

open Set Topology TopologicalSpace CountableNetwork

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

example (N : Set (Set X)) : IsNetwork N ↔
    (∀ U, IsOpen U → ∀ x ∈ U, ∃ A ∈ N, x ∈ A ∧ A ⊆ U) := Iff.rfl

example : HasCountableNetwork X ↔ ∃ N : Set (Set X), N.Countable ∧ IsNetwork N :=
  Iff.rfl

example [NormalSpace X] [T3Space X]
    {N : Set (Set X)} (hN : IsNetwork N) :
    ∃ f : (N × N) → C(X, ℝ),
      (∀ i x, f i x ∈ Icc (0 : ℝ) 1) ∧
      Pairwise (fun x y => ∃ i, f i x ≠ f i y) :=
  CountableNetwork.IsNetwork.exists_bounded_separating_family hN

example [CompactSpace X] [T2Space X]
    {N : Set (Set X)} (hc : N.Countable) (hN : IsNetwork N) : MetrizableSpace X :=
  CountableNetwork.metrizableSpace_of_countable_network hc hN

example [SecondCountableTopology X] :
    HasCountableNetwork X :=
  CountableNetwork.hasCountableNetwork_of_secondCountable

example [CompactSpace X] [T2Space X] :
    MetrizableSpace X ↔ HasCountableNetwork X :=
  CountableNetwork.metrizable_iff_hasCountableNetwork

example [CompactSpace X] [T2Space X] :
    SecondCountableTopology X ↔ HasCountableNetwork X :=
  CountableNetwork.secondCountable_iff_hasCountableNetwork

example [CompactSpace X] [T2Space X]
    (h : HasCountableNetwork X) :
    ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace X› :=
  CountableNetwork.exists_compatibleMetric h

example [CompactSpace X] [T2Space X]
    {N : Set (Set X)} (hN : IsNetwork N) :
    ∃ F : X → ((N × N) → ℝ), IsClosedEmbedding F ∧
      ∀ x i, F x i ∈ Icc (0 : ℝ) 1 :=
  CountableNetwork.IsNetwork.exists_closedEmbedding hN

example {N : Set (Set X)} (hN : IsNetwork N) {f : X → Y}
    (hf : Continuous f) (hs : Function.Surjective f) : IsNetwork ((Set.image f) '' N) :=
  CountableNetwork.IsNetwork.image hN hf hs

example (h : HasCountableNetwork X)
    {f : X → Y} (hf : Continuous f) (hs : Function.Surjective f) :
    HasCountableNetwork Y :=
  CountableNetwork.HasCountableNetwork.of_continuous_surjective h hf hs

example (h : HasCountableNetwork X) (S : Set X) :
    HasCountableNetwork S :=
  CountableNetwork.HasCountableNetwork.subtype h S

example [T2Space X] (h : HasCountableNetwork X)
    {S : Set X} (hS : IsCompact S) : MetrizableSpace S :=
  CountableNetwork.metrizable_compact_subspace h hS
