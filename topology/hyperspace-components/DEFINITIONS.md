# Pinned definitions

`ProperContinuum X` is the subtype of Mathlib nonempty compact sets that are connected and have underlying set different from the whole ambient space. Its topology is induced from the Vietoris hyperspace; for a metric space this agrees with the Hausdorff metric topology. The classification uses Mathlib `Joined` and `pathComponent` literally in this subtype.

The local composant predicate is the union of all proper nonempty compact connected sets through a point. No extra point is adjoined. Indecomposability means that two proper subcontinua cannot cover the ambient space. The proofs do not assume a path, a common continuum or the classification inside any definition.

Complete upstream files are retained as inert text snapshots, with licenses, immutable commit and blob identities, byte counts and SHA-256 hashes. The index checks whole declaration tails and cross-references. The bounded source-layout checker is not a general Lean parser. Separate Lean audits elaborate the semantic forms against the actual pinned dependencies.

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

## unitInterval

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UnitInterval.lean#L32)

```lean
abbrev unitInterval : Set ℝ :=
  Set.Icc 0 1
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

## Set.Countable

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Countable.lean#L49)

```lean
protected def Countable (s : Set α) : Prop := Countable s
```

## Countable

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Countable/Defs.lean#L41)

```lean
class Countable (α : Sort u) : Prop where
  /-- A type `α` is countable if there exists an injective map `α → ℕ`. -/
  exists_injective_nat' : ∃ f : α → ℕ, Injective f
```

## Set.range

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean#L173)

```lean
def range (f : ι → α) : Set α := {x | ∃ y, f y = x}
```

## ConnectedSpace

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Connected/Basic.lean#L705)

```lean
class ConnectedSpace (α : Type u) [TopologicalSpace α] : Prop extends PreconnectedSpace α where
  /-- A connected space is nonempty. -/
  toNonempty : Nonempty α
```

## Nontrivial

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Nontrivial/Defs.lean#L28)

```lean
class Nontrivial (α : Type*) : Prop where
  /-- In a nontrivial type, there exists a pair of distinct terms. -/
  exists_pair_ne : ∃ x y : α, x ≠ y
```

## Subsingleton

[Pinned source](https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Core.lean#L1267)

```lean
class Subsingleton (α : Sort u) : Prop where
  /-- Prove that `α` is a subsingleton by showing that any two elements are equal. -/
  intro ::
  /-- Any two elements of a subsingleton are equal. -/
  allEq : (a b : α) → a = b
```

## Path

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Path.lean#L60)

```lean
structure Path (x y : X) extends C(I, X) where
  /-- The start point of a `Path`. -/
  source' : toFun 0 = x
  /-- The end point of a `Path`. -/
  target' : toFun 1 = y
```

## ContinuousMap

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/ContinuousMap/Defs.lean#L33)

```lean
structure ContinuousMap (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] where
  /-- The function `X → Y` -/
  protected toFun : X → Y
  /-- Proposition that `toFun` is continuous -/
  protected continuous_toFun : Continuous toFun := by fun_prop
```

## Joined

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Connected/PathConnected.lean#L62)

```lean
def Joined (x y : X) : Prop :=
  Nonempty (Path x y)
```

## pathComponent

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Connected/PathConnected.lean#L291)

```lean
def pathComponent (x : X) :=
  { y | Joined x y }
```

## Local literal predicates

The following complete definitions appear independently in Challenge and are compared with the Solution values as raw Lean expressions.

```lean
def IsSubcontinuum (K : Set X) : Prop := IsCompact K ∧ IsConnected K
```

```lean
def IsIndecomposable (X : Type u) [tX : TopologicalSpace X] : Prop :=
  ∀ K L : Set X, IsSubcontinuum K → IsSubcontinuum L →
    K ∪ L = univ → K = univ ∨ L = univ
```

```lean
def composant (x : X) : Set X :=
  {y | ∃ K : Set X, IsSubcontinuum K ∧ K ≠ univ ∧ x ∈ K ∧ y ∈ K}
```

```lean
def familyUnion (γ : unitInterval → NonemptyCompacts X) (s : Set unitInterval) : Set X :=
  ⋃ (t : unitInterval) (_ht : t ∈ s), (γ t : Set X)
```

```lean
abbrev ProperContinuum (X : Type*) [tX : TopologicalSpace X] :=
  {K : NonemptyCompacts X // IsConnected (K : Set X) ∧ (K : Set X) ≠ univ}
```

## Complete checkpoint engines

### Vietoris connected family union

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Sets/VietorisTopology.lean#L391)

```lean
theorem isPreconnected_biUnion {s : Set α} {f : α → Set β} (hs : IsPreconnected s)
    (hf : ContinuousOn f s) (h : ∃ x ∈ s, IsPreconnected (f x)) :
    IsPreconnected (⋃ x ∈ s, f x) := by
  rw [← sUnion_image]
  exact isPreconnected_sUnion (hs.image _ hf) (by grind)
```

### Vietoris compact family union

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Sets/VietorisTopology.lean#L1033)

```lean
theorem isCompact_biUnion_coe_of_isCompact {S : Set (NonemptyCompacts α)} (hs : IsCompact S) :
    IsCompact (⋃ K ∈ S, (K : Set α)) := by
  convert! Compacts.isCompact_biUnion_coe_of_isCompact (hs.image continuous_toCompacts)
  simp_rw [biUnion_image, coe_toCompacts]
```

### finite ordered interval subdivision

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UnitInterval.lean#L481)

```lean
lemma exists_monotone_Icc_subset_open_cover_unitInterval {ι} {c : ι → Set I}
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : univ ⊆ ⋃ i, c i) : ∃ t : ℕ → I, t 0 = 0 ∧
      Monotone t ∧ (∃ n, ∀ m ≥ n, t m = 1) ∧ ∀ n, ∃ i, Icc (t n) (t (n + 1)) ⊆ c i := by
  simp_rw [← Subtype.coe_inj]
  exact exists_monotone_Icc_subset_open_cover_Icc zero_le_one hc₁ hc₂
```

