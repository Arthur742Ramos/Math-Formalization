# Definitions, selected contracts and dependencies

All declarations are in `CountableNetwork`; both underlying types have arbitrary universes and canonical supplied topologies. Challenge and Solution are checked separately. The two selected names below are actual definitions, and contract tests check their literal bodies by `Iff.rfl`.

```lean
def IsNetwork (N : Set (Set X)) : Prop :=
  ∀ U, IsOpen U → ∀ x ∈ U, ∃ A ∈ N, x ∈ A ∧ A ⊆ U

def HasCountableNetwork (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ N : Set (Set X), N.Countable ∧ IsNetwork N
```

Network members carry no openness/closedness/neighborhood condition. Countability applies to the family itself; subtype `N` and its square become encodable without assuming nonemptiness. Open-set and neighborhood formulations agree by choosing an open neighborhood inside any neighborhood.

The following are the eleven selected signatures. Ambient variables are `{X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]`; every extra instance is displayed explicitly. Names beginning `IsNetwork.` or `HasCountableNetwork.` are qualified within `CountableNetwork`.

```lean
theorem IsNetwork.exists_bounded_separating_family [NormalSpace X] [T3Space X]
    {N : Set (Set X)} (hN : IsNetwork N) :
    ∃ f : (N × N) → C(X, ℝ),
      (∀ i x, f i x ∈ Icc (0 : ℝ) 1) ∧
      Pairwise (fun x y => ∃ i, f i x ≠ f i y)
```

```lean
theorem metrizableSpace_of_countable_network [CompactSpace X] [T2Space X]
    {N : Set (Set X)} (hc : N.Countable) (hN : IsNetwork N) : MetrizableSpace X
```

```lean
theorem hasCountableNetwork_of_secondCountable [SecondCountableTopology X] :
    HasCountableNetwork X
```

```lean
theorem metrizable_iff_hasCountableNetwork [CompactSpace X] [T2Space X] :
    MetrizableSpace X ↔ HasCountableNetwork X
```

```lean
theorem secondCountable_iff_hasCountableNetwork [CompactSpace X] [T2Space X] :
    SecondCountableTopology X ↔ HasCountableNetwork X
```

```lean
theorem exists_compatibleMetric [CompactSpace X] [T2Space X]
    (h : HasCountableNetwork X) :
    ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace X›
```

```lean
theorem IsNetwork.exists_closedEmbedding [CompactSpace X] [T2Space X]
    {N : Set (Set X)} (hN : IsNetwork N) :
    ∃ F : X → ((N × N) → ℝ), IsClosedEmbedding F ∧
      ∀ x i, F x i ∈ Icc (0 : ℝ) 1
```

```lean
theorem IsNetwork.image {N : Set (Set X)} (hN : IsNetwork N) {f : X → Y}
    (hf : Continuous f) (hs : Function.Surjective f) : IsNetwork ((Set.image f) '' N)
```

```lean
theorem HasCountableNetwork.of_continuous_surjective (h : HasCountableNetwork X)
    {f : X → Y} (hf : Continuous f) (hs : Function.Surjective f) :
    HasCountableNetwork Y
```

```lean
theorem HasCountableNetwork.subtype (h : HasCountableNetwork X) (S : Set X) :
    HasCountableNetwork S
```

```lean
theorem metrizable_compact_subspace [T2Space X] (h : HasCountableNetwork X)
    {S : Set X} (hS : IsCompact S) : MetrizableSpace S
```

The first bridge uses normality and T3 separation, with no compactness or countability. Compact Hausdorff spaces supply those instances. The closed embedding is a map into a real product indexed by the given network squared; bounded coordinates do not change its literal codomain. Image transport and heredity do not require separation or compactness. The compact-subspace result needs only ambient Hausdorff separation, an ambient countable network and compactness of the chosen subspace.

Canonical upstream definitions include countability, continuous maps, closed embeddings, product topology, compactness, Hausdorff separation, second countability and metrizability. No project-local replacement topology or weakened metric is introduced. The selected compatible metric has topology equal to the supplied topology, not merely an unspecified homeomorphic topology.
