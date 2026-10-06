# Pinned definitions

The statement uses Mathlib’s nonempty compact sets, ordinary connectedness, the real unit interval, and strict subset inclusion. Continuity and embedding refer to the Vietoris topology, which agrees with the Hausdorff metric topology at this pin. No project predicate assumes an arc or a parametrization.

The manifest records complete declaration ranges and SHA-256 hashes. Full unmodified upstream files, including their headers, are retained as inert `.txt` snapshots. Each Mathlib source matches the previously qualified complete source inventory at the exact pin. The checker verifies complete declaration tails, cross-references, and installed dependency bytes. It also rejects corrupted sources, wrong pins, missing definitions, and truncated structure fields.

The local source-layout checker is bounded to the retained declarations; it is not a general Lean parser. `scripts/DefinitionAudit.lean` elaborates ordinary semantic forms against the actual dependencies. `scripts/SemanticAudit.lean` checks the project definitions by reflexivity, strict endpoint separation, and the singleton edge case.

## MetricSpace

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Defs.lean#L70)

```lean
class MetricSpace (α : Type u) : Type u extends PseudoMetricSpace α where
  eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y
```

## PseudoMetricSpace

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L141)

```lean
class PseudoMetricSpace (α : Type u) : Type u extends Dist α where
  dist_self : ∀ x : α, dist x x = 0
  dist_comm : ∀ x y : α, dist x y = dist y x
  dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z
  /-- Extended distance between two points -/
  edist : α → α → ℝ≥0∞ := fun x y => ENNReal.ofNNReal (.mk (dist x y) (dist_nonneg' _ ‹_› ‹_› ‹_›))
  edist_dist : ∀ x y : α, edist x y = ENNReal.ofReal (dist x y) := by
    intro x y; exact ENNReal.coe_nnreal_eq _
  toUniformSpace : UniformSpace α := .ofDist dist dist_self dist_comm dist_triangle
  uniformity_dist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | dist p.1 p.2 < ε } := by intros; rfl
  toBornology : Bornology α := Bornology.ofDist dist dist_comm dist_triangle
  cobounded_sets : (Bornology.cobounded α).sets =
    { s | ∃ C : ℝ, ∀ x ∈ sᶜ, ∀ y ∈ sᶜ, dist x y ≤ C } := by intros; rfl
```

## CompactSpace

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L297)

```lean
class CompactSpace : Prop where
  /-- In a compact space, `Set.univ` is a compact set. -/
  isCompact_univ : IsCompact (Set.univ : Set X)
```

## IsCompact

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L290)

```lean
def IsCompact (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f
```

## IsConnected

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Connected/Basic.lean#L55)

```lean
def IsConnected (s : Set α) : Prop :=
  s.Nonempty ∧ IsPreconnected s
```

## IsPreconnected

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Connected/Basic.lean#L50)

```lean
def IsPreconnected (s : Set α) : Prop :=
  ∀ u v : Set α, IsOpen u → IsOpen v → s ⊆ u ∪ v → (s ∩ u).Nonempty → (s ∩ v).Nonempty →
    (s ∩ (u ∩ v)).Nonempty
```

## TopologicalSpace

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L73)

```lean
class TopologicalSpace (X : Type u) where
  /-- A predicate saying that a set is an open set. Use `IsOpen` in the root namespace instead. -/
  protected IsOpen : Set X → Prop
  /-- The set representing the whole space is an open set.
  Use `isOpen_univ` in the root namespace instead. -/
  protected isOpen_univ : IsOpen univ
  /-- The intersection of two open sets is an open set. Use `IsOpen.inter` instead. -/
  protected isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  /-- The union of a family of open sets is an open set.
  Use `isOpen_sUnion` in the root namespace instead. -/
  protected isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)
```

## Continuous

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L155)

```lean
structure Continuous (f : X → Y) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
```

## Topology.IsEmbedding

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean#L147)

```lean
structure IsEmbedding (f : X → Y) : Prop extends IsInducing f where
  /-- A topological embedding is injective. -/
  injective : Function.Injective f
```

## Topology.IsInducing

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean#L132)

```lean
structure IsInducing (f : X → Y) : Prop where
  /-- The topology on the domain is equal to the induced topology. -/
  eq_induced : tX = tY.induced f
```

## unitInterval

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UnitInterval.lean#L32)

```lean
abbrev unitInterval : Set ℝ :=
  Set.Icc 0 1
```

## StrictMono

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Monotone/Defs.lean#L86)

```lean
def StrictMono (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a < b → f a < f b
```

## TopologicalSpace.Compacts

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Sets/Compacts.lean#L38)

```lean
structure Compacts (α : Type*) [TopologicalSpace α] where
  /-- the carrier set, i.e. the points in this set -/
  carrier : Set α
  isCompact' : IsCompact carrier
```

## TopologicalSpace.NonemptyCompacts

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Sets/Compacts.lean#L399)

```lean
structure NonemptyCompacts (α : Type*) [TopologicalSpace α] extends Compacts α where
  nonempty' : carrier.Nonempty
```

## NonemptyCompacts SetLike

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Sets/Compacts.lean#L404)

```lean
instance : SetLike (NonemptyCompacts α) α where
  coe s := s.carrier
  coe_injective s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr
```

## NonemptyCompacts inclusion order

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Sets/Compacts.lean#L411)

```lean
instance : PartialOrder (NonemptyCompacts α) := .ofSetLike (NonemptyCompacts α) α
```

## NonemptyCompacts topology

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Sets/VietorisTopology.lean#L825)

```lean
instance topology : TopologicalSpace (NonemptyCompacts α) :=
  .induced (↑) (.vietoris α)
```

## NonemptyCompacts MetricSpace

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Closeds.lean#L293)

```lean
instance : MetricSpace (NonemptyCompacts α) :=
  EMetricSpace.toMetricSpace fun x y =>
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded x.nonempty y.nonempty x.isCompact.isBounded
      y.isCompact.isBounded
```

## subtype topology

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean#L76)

```lean
instance _root_.instTopologicalSpaceSubtype {p : X → Prop} [t : TopologicalSpace X] :
    TopologicalSpace (Subtype p) :=
  induced (↑) t
```

## Set.Subset

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L89)

```lean
protected def Subset (s₁ s₂ : Set α) :=
  ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂
```

## Set.Nonempty

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L280)

```lean
protected def Nonempty (s : Set α) : Prop :=
  ∃ x, x ∈ s
```

## Metric.infDist

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/HausdorffDistance.lean#L463)

```lean
def infDist (x : α) (s : Set α) : ℝ :=
  ENNReal.toReal (infEDist x s)
```

## Project definitions

`OrderArcs.ContinuumInterval A B` is the subtype of nonempty compact sets `K` satisfying `A ≤ K`, `K ≤ B`, and `IsConnected (K : Set X)`. `OrderArcs.height q K` is the negative weighted sum of distance-to-set coordinates, with weights `(1/2)^(n+1)`. Both definitions are written independently in Challenge and their raw values are compared exactly with Solution. The scalar is not normalized on singleton sets.
