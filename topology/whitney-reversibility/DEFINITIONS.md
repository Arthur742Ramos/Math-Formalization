# Literal definitions and pinned sources

`Continuum X` is the subtype of nonempty compact sets whose underlying set is connected, with the induced Vietoris topology and Hausdorff metric. A Whitney map is literally continuous, zero on every singleton, and strictly increasing for proper inclusion. A size map uses weak inclusion increase. No covering family, decomposition, or theorem conclusion occurs in either map predicate.

`IsDecomposable K` requires two proper nonempty compact connected subsets whose union is K. `IsHereditarilyDecomposable S` applies this to every nondegenerate compact connected subset of S. Thus singletons are hereditarily decomposable, while a nondegenerate indecomposable subcontinuum is an obstruction. The sequential theorem uses the literal filter `Tendsto`, natural-number `atTop`, and real neighborhood filter at zero.

Each retained upstream file is complete and includes its source header. The manifest records exact commits, Git blob identities, byte counts, SHA-256 hashes, complete declaration ranges, cross-references, and upstream licenses. Local definitions are compared with the independently compiled Challenge as raw Lean expressions. The layout checker is bounded to these indexed sources.

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

## ConnectedSpace

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Connected/Basic.lean#L705)

```lean
class ConnectedSpace (α : Type u) [TopologicalSpace α] : Prop extends PreconnectedSpace α where
  /-- A connected space is nonempty. -/
  toNonempty : Nonempty α
```

## Set.Nontrivial

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Subsingleton.lean#L153)

```lean
protected def Nontrivial (s : Set α) : Prop :=
  ∃ x ∈ s, ∃ y ∈ s, x ≠ y
```

## Filter.Tendsto

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L422)

```lean
def Tendsto (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.map f ≤ l₂
```

## Filter.atTop

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/AtTopBot/Defs.lean#L39)

```lean
def atTop [Preorder α] : Filter α :=
  ⨅ a, 𝓟 (Ici a)
```

## nhds

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L130)

```lean
irreducible_def nhds (x : X) : Filter X :=
  ⨅ s ∈ { s : Set X | x ∈ s ∧ IsOpen s }, 𝓟 s
```

## Monotone

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Monotone/Defs.lean#L62)

```lean
def Monotone (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f a ≤ f b
```

## StrictMono

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Monotone/Defs.lean#L86)

```lean
def StrictMono (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a < b → f a < f b
```

## connected closed-fiber preimage

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Connected/Clopen.lean#L404)

```lean
theorem Topology.IsCoinducing.isConnected_preimage_of_isClosed
    (connected_fibers : ∀ t : β, IsConnected (f ⁻¹' {t}))
    (hcl : IsCoinducing f) {t : Set β} (ht : IsClosed t) (ht' : IsConnected t) :
    IsConnected (f ⁻¹' t) := by
  -- The following proof is essentially https://stacks.math.columbia.edu/tag/0377
  -- although the statement is slightly different
  have hf : Surjective f := Surjective.of_comp fun t : β => (connected_fibers t).1
  refine ⟨Nonempty.preimage ht'.nonempty hf, ?_⟩
  have hT : IsClosed (f ⁻¹' t) :=
    hcl.isClosed_preimage.mpr ht
  -- To show it's preconnected we decompose (f ⁻¹' t) as a subset of two
  -- closed disjoint sets in α. We want to show that it's a subset of either.
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hT]
  intro u v hu hv huv uv_disj
  -- To do this we decompose t into T₁ and T₂
  -- we will show that t is a subset of either and hence
  -- (f ⁻¹' t) is a subset of u or v
  let T₁ := { t' ∈ t | f ⁻¹' {t'} ⊆ u }
  let T₂ := { t' ∈ t | f ⁻¹' {t'} ⊆ v }
  have fiber_decomp : ∀ t' ∈ t, f ⁻¹' {t'} ⊆ u ∨ f ⁻¹' {t'} ⊆ v := by
    intro t' ht'
    apply isPreconnected_iff_subset_of_disjoint_closed.1 (connected_fibers t').2 u v hu hv
    · exact Subset.trans (preimage_mono (singleton_subset_iff.2 ht')) huv
    rw [uv_disj.inter_eq, inter_empty]
  have T₁_u : f ⁻¹' T₁ = f ⁻¹' t ∩ u := by
    apply eq_of_subset_of_subset
    · rw [← biUnion_preimage_singleton]
      refine iUnion₂_subset fun t' ht' => subset_inter ?_ ht'.2
      rw [hf.preimage_subset_preimage_iff, singleton_subset_iff]
      exact ht'.1
    rintro a ⟨hat, hau⟩
    constructor
    · exact mem_preimage.1 hat
    refine (fiber_decomp (f a) (mem_preimage.1 hat)).resolve_right fun h => ?_
    exact uv_disj.subset_compl_right hau (h rfl)
  -- This proof is exactly the same as the above (modulo some symmetry)
  have T₂_v : f ⁻¹' T₂ = f ⁻¹' t ∩ v := by
    apply eq_of_subset_of_subset
    · rw [← biUnion_preimage_singleton]
      refine iUnion₂_subset fun t' ht' => subset_inter ?_ ht'.2
      rw [hf.preimage_subset_preimage_iff, singleton_subset_iff]
      exact ht'.1
    rintro a ⟨hat, hav⟩
    constructor
    · exact mem_preimage.1 hat
    · refine (fiber_decomp (f a) (mem_preimage.1 hat)).resolve_left fun h => ?_
      exact uv_disj.subset_compl_left hav (h rfl)
  -- Now we show T₁, T₂ are closed, cover t and are disjoint.
  have hT₁ : IsClosed T₁ := hcl.isClosed_preimage.mp (T₁_u.symm ▸ IsClosed.inter hT hu)
  have hT₂ : IsClosed T₂ := hcl.isClosed_preimage.mp (T₂_v.symm ▸ IsClosed.inter hT hv)
  have T_decomp : t ⊆ T₁ ∪ T₂ := fun t' ht' => by
    rw [mem_union t' T₁ T₂]
    rcases fiber_decomp t' ht' with htu | htv
    · left; exact ⟨ht', htu⟩
    · right; exact ⟨ht', htv⟩
  have T_disjoint : Disjoint T₁ T₂ := by
    refine Disjoint.of_preimage hf ?_
    rw [T₁_u, T₂_v, disjoint_iff_inter_eq_empty, ← inter_inter_distrib_left, uv_disj.inter_eq,
      inter_empty]
  -- Now we do cases on whether t is a subset of T₁ or T₂ to show
  -- that the preimage is a subset of u or v.
  rcases (isPreconnected_iff_subset_of_fully_disjoint_closed ht).1
    ht'.isPreconnected T₁ T₂ hT₁ hT₂ T_decomp T_disjoint with h | h
  · left
    rw [Subset.antisymm_iff] at T₁_u
    suffices f ⁻¹' t ⊆ f ⁻¹' T₁
      from (this.trans T₁_u.1).trans inter_subset_right
    exact preimage_mono h
  · right
    rw [Subset.antisymm_iff] at T₂_v
    suffices f ⁻¹' t ⊆ f ⁻¹' T₂
      from (this.trans T₂_v.1).trans inter_subset_right
    exact preimage_mono h
```

## compact continuous minimum

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order/Compact.lean#L228)

```lean
theorem IsCompact.exists_isMinOn [ClosedIicTopology α] {s : Set β} (hs : IsCompact s)
    (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) : ∃ x ∈ s, IsMinOn f s x := by
  rcases (hs.image_of_continuousOn hf).exists_isLeast (ne_s.image f) with ⟨_, ⟨x, hxs, rfl⟩, hx⟩
  refine ⟨x, hxs, forall_mem_image.1 (fun _ hb => hx <| mem_image_of_mem f ?_)⟩
  rwa [(image_id' s).symm]
```

## Vietoris connected family union

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Sets/VietorisTopology.lean#L391)

```lean
theorem isPreconnected_biUnion {s : Set α} {f : α → Set β} (hs : IsPreconnected s)
    (hf : ContinuousOn f s) (h : ∃ x ∈ s, IsPreconnected (f x)) :
    IsPreconnected (⋃ x ∈ s, f x) := by
  rw [← sUnion_image]
  exact isPreconnected_sUnion (hs.image _ hf) (by grind)
```

## Vietoris compact family union

[Pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Sets/VietorisTopology.lean#L1033)

```lean
theorem isCompact_biUnion_coe_of_isCompact {S : Set (NonemptyCompacts α)} (hs : IsCompact S) :
    IsCompact (⋃ K ∈ S, (K : Set α)) := by
  convert! Compacts.isCompact_biUnion_coe_of_isCompact (hs.image continuous_toCompacts)
  simp_rw [biUnion_image, coe_toCompacts]
```

## Local definitions

These definitions are independently stated in Challenge and compared as literal values.

```lean
abbrev Continuum (X : Type u) [tX : TopologicalSpace X] :=
  {K : NonemptyCompacts X // IsConnected (K : Set X)}
```

```lean
def singleton (x : X) : Continuum X := ⟨{x}, isConnected_singleton⟩
```

```lean
def whole [cnX : ConnectedSpace X] : Continuum X :=
  ⟨⟨⟨univ, isCompact_univ⟩, Set.univ_nonempty⟩, isConnected_univ⟩
```

```lean
def IsWhitneyMap (μ : Continuum X → ℝ) : Prop :=
  Continuous μ ∧ (∀ x, μ (singleton x) = 0) ∧
    ∀ A B : Continuum X, A.val < B.val → μ A < μ B
```

```lean
def IsSizeMap (σ : Continuum X → ℝ) : Prop :=
  Continuous σ ∧ (∀ x, σ (singleton x) = 0) ∧
    ∀ A B : Continuum X, A.val ≤ B.val → σ A ≤ σ B
```

```lean
def relativeLevel (σ : Continuum X → ℝ) (Y : Continuum X) (t : ℝ) :
    Set (Continuum X) := {K | K.val ≤ Y.val ∧ σ K = t}
```

```lean
def familyUnion (S : Set (Continuum X)) : Set X :=
  ⋃ (K : Continuum X) (_hK : K ∈ S), (K.val : Set X)
```

```lean
def IsDecomposable {A : Type v} [tA : TopologicalSpace A] (K : Set A) : Prop :=
  ∃ P Q : Set A, IsCompact P ∧ IsConnected P ∧ IsCompact Q ∧ IsConnected Q ∧
    P ⊆ K ∧ Q ⊆ K ∧ P ≠ K ∧ Q ≠ K ∧ P ∪ Q = K
```

```lean
def IsHereditarilyDecomposable {A : Type v} [tA : TopologicalSpace A] (S : Set A) : Prop :=
  ∀ K : Set A, K ⊆ S → IsCompact K → IsConnected K → K.Nontrivial → IsDecomposable K
```

