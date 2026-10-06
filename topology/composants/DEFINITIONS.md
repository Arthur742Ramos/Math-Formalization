# Definition fidelity

The ambient type is the continuum with its own topology. `IsSubcontinuum`
requires compactness and nonempty connectedness. The literal `composant x` is
the union of proper subcontinua containing `x`; it is empty in a singleton
space. The eight foundation statements retain their explicit nondegeneracy
and second-countability assumptions. Relative statements use the actual
induced topology on a continuum subtype.

The Alexandroff theorem chooses one ambient open cover before all partitions,
target types, target topologies and maps. Massive sets mean sets with nonempty
interiors. A partition is closed, and its complement has two disjoint open
sides containing the given closed sets. `IsOmegaMap` includes continuity and
literal inverse-image refinement on the induced partition subtype.
Surjectivity is a separate hypothesis. A target continuum is nonempty,
compact, connected and Hausdorff; it can occupy an independent universe and
need not be metrizable.

The metric class includes a compatible topology through its uniform-space
fields. The compact-set and Vietoris bodies document the compact-limit
construction used in the proof. The source dossier preserves complete files,
license and attribution headers, immutable source identities and complete
indexed declaration bodies. Evidence text files are not imported modules.
The seven project predicates are independently repeated in Challenge and
compared as raw Lean expressions, including universe lists and definition values.

## TopologicalSpace

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean), lines 73 to 83.

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

## IsOpen

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean), lines 95 to 95.

```lean
def IsOpen : Set X → Prop := TopologicalSpace.IsOpen
```

## IsClosed

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean), lines 107 to 109.

```lean
class IsClosed (s : Set X) : Prop where
  /-- The complement of a closed set is an open set. -/
  isOpen_compl : IsOpen sᶜ
```

## IsPreconnected

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Connected/Basic.lean), lines 50 to 52.

```lean
def IsPreconnected (s : Set α) : Prop :=
  ∀ u v : Set α, IsOpen u → IsOpen v → s ⊆ u ∪ v → (s ∩ u).Nonempty → (s ∩ v).Nonempty →
    (s ∩ (u ∩ v)).Nonempty
```

## IsConnected

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Connected/Basic.lean), lines 55 to 56.

```lean
def IsConnected (s : Set α) : Prop :=
  s.Nonempty ∧ IsPreconnected s
```

## PreconnectedSpace

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Connected/Basic.lean), lines 697 to 699.

```lean
class PreconnectedSpace (α : Type u) [TopologicalSpace α] : Prop where
  /-- The universal set `Set.univ` in a preconnected space is a preconnected set. -/
  isPreconnected_univ : IsPreconnected (univ : Set α)
```

## ConnectedSpace

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Connected/Basic.lean), lines 705 to 707.

```lean
class ConnectedSpace (α : Type u) [TopologicalSpace α] : Prop extends PreconnectedSpace α where
  /-- A connected space is nonempty. -/
  toNonempty : Nonempty α
```

## CompactSpace

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean), lines 297 to 299.

```lean
class CompactSpace : Prop where
  /-- In a compact space, `Set.univ` is a compact set. -/
  isCompact_univ : IsCompact (Set.univ : Set X)
```

## IsCompact

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean), lines 290 to 291.

```lean
def IsCompact (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f
```

## isCompact_iff_finite_subcover

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Compact.lean), lines 386 to 389.

```lean
theorem isCompact_iff_finite_subcover :
    IsCompact s ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) → ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  ⟨fun hs => hs.elim_finite_subcover, isCompact_of_finite_subcover⟩
```

## T2Space

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/Hausdorff.lean), lines 85 to 87.

```lean
class T2Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Every two points in a Hausdorff space admit disjoint open neighbourhoods. -/
  t2 : Pairwise fun x y => ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v
```

## interior

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean), lines 122 to 123.

```lean
def interior (s : Set X) : Set X :=
  ⋃₀ { t | IsOpen t ∧ t ⊆ s }
```

## closure

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean), lines 126 to 127.

```lean
def closure (s : Set X) : Set X :=
  ⋂₀ { t | IsClosed t ∧ s ⊆ t }
```

## IsNowhereDense

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean), lines 200 to 200.

```lean
def IsNowhereDense (s : Set X) := interior (closure s) = ∅
```

## Nontrivial

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Nontrivial/Defs.lean), lines 28 to 30.

```lean
class Nontrivial (α : Type*) : Prop where
  /-- In a nontrivial type, there exists a pair of distinct terms. -/
  exists_pair_ne : ∃ x y : α, x ≠ y
```

## subtype topology

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean), lines 76 to 78.

```lean
instance _root_.instTopologicalSpaceSubtype {p : X → Prop} [t : TopologicalSpace X] :
    TopologicalSpace (Subtype p) :=
  induced (↑) t
```

## TopologicalSpace.induced

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean), lines 64 to 74.

```lean
def induced (f : X → Y) (t : TopologicalSpace Y) : TopologicalSpace X where
  IsOpen s := ∃ t, IsOpen t ∧ f ⁻¹' t = s
  isOpen_univ := ⟨univ, isOpen_univ, preimage_univ⟩
  isOpen_inter := by
    rintro s₁ s₂ ⟨s'₁, hs₁, rfl⟩ ⟨s'₂, hs₂, rfl⟩
    exact ⟨s'₁ ∩ s'₂, hs₁.inter hs₂, preimage_inter⟩
  isOpen_sUnion S h := by
    choose! g hgo hfg using h
    refine ⟨⋃₀ (g '' S), isOpen_sUnion <| forall_mem_image.2 hgo, ?_⟩
    rw [preimage_sUnion, biUnion_image, sUnion_eq_biUnion]
    exact iUnion₂_congr hfg
```

## Dense

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean), lines 146 to 147.

```lean
def Dense (s : Set X) : Prop :=
  ∀ x, x ∈ closure s
```

## BaireSpace

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean), lines 239 to 240.

```lean
class BaireSpace (X : Type*) [TopologicalSpace X] : Prop where
  baire_property : ∀ f : ℕ → Set X, (∀ n, IsOpen (f n)) → (∀ n, Dense (f n)) → Dense (⋂ n, f n)
```

## SecondCountableTopology

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean), lines 793 to 795.

```lean
class _root_.SecondCountableTopology : Prop where
  /-- There exists a countable set of sets that generates the topology. -/
  is_open_generated_countable : ∃ b : Set (Set α), b.Countable ∧ t = TopologicalSpace.generateFrom b
```

## IsTopologicalBasis

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean), lines 73 to 79.

```lean
structure IsTopologicalBasis (s : Set (Set α)) : Prop where
  /-- For every point `x`, the set of `t ∈ s` such that `x ∈ t` is directed downwards. -/
  exists_subset_inter : ∀ t₁ ∈ s, ∀ t₂ ∈ s, ∀ x ∈ t₁ ∩ t₂, ∃ t₃ ∈ s, x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂
  /-- The sets from `s` cover the whole space. -/
  sUnion_eq : ⋃₀ s = univ
  /-- The topology is generated by sets from `s`. -/
  eq_generateFrom : t = generateFrom s
```

## countableBasis

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean), lines 826 to 827.

```lean
def countableBasis [SecondCountableTopology α] : Set (Set α) :=
  (exists_countable_basis α).choose
```

## connectedComponent

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Connected/Basic.lean), lines 495 to 496.

```lean
def connectedComponent (x : α) : Set α :=
  ⋃₀ { s : Set α | IsPreconnected s ∧ x ∈ s }
```

## connectedComponentIn

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Connected/Basic.lean), lines 505 to 506.

```lean
noncomputable def connectedComponentIn (F : Set α) (x : α) : Set α :=
  if h : x ∈ F then (↑) '' connectedComponent (⟨x, h⟩ : F) else ∅
```

## IsMeagre

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean), lines 284 to 284.

```lean
def IsMeagre (s : Set X) := sᶜ ∈ residual X
```

## residual

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean), lines 170 to 171.

```lean
def residual (X : Type*) [TopologicalSpace X] : Filter X :=
  Filter.countableGenerate { t | IsOpen t ∧ Dense t }
```

## Filter.countableGenerate

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/CountableInter.lean), lines 281 to 283.

```lean
def countableGenerate : Filter α :=
  ofCountableInter {s | CountableGenerateSets g s} (fun _ ↦ .sInter) fun _ _ ↦ .superset
deriving CountableInterFilter
```

## Filter.CountableGenerateSets

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/CountableInter.lean), lines 272 to 277.

```lean
inductive CountableGenerateSets : Set α → Prop
  | basic {s : Set α} : s ∈ g → CountableGenerateSets s
  | univ : CountableGenerateSets univ
  | superset {s t : Set α} : CountableGenerateSets s → s ⊆ t → CountableGenerateSets t
  | sInter {S : Set (Set α)} :
    S.Countable → (∀ s ∈ S, CountableGenerateSets s) → CountableGenerateSets (⋂₀ S)
```

## Countable

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Countable/Defs.lean), lines 41 to 43.

```lean
class Countable (α : Sort u) : Prop where
  /-- A type `α` is countable if there exists an injective map `α → ℕ`. -/
  exists_injective_nat' : ∃ f : α → ℕ, Injective f
```

## Set.Countable

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Countable.lean), lines 49 to 49.

```lean
protected def Countable (s : Set α) : Prop := Countable s
```

## Set.range

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean), lines 173 to 173.

```lean
def range (f : ι → α) : Set α := {x | ∃ y, f y = x}
```

## Continuous

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean), lines 155 to 158.

```lean
structure Continuous (f : X → Y) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
```

## MetricSpace

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Defs.lean), lines 70 to 71.

```lean
class MetricSpace (α : Type u) : Type u extends PseudoMetricSpace α where
  eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y
```

## PseudoMetricSpace

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean), lines 141 to 153.

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

## Dist

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean), lines 104 to 106.

```lean
class Dist (α : Type*) where
  /-- Distance between two points -/
  dist : α → α → ℝ
```

## Metric.ball

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean), lines 370 to 371.

```lean
def ball (x : α) (ε : ℝ) : Set α :=
  { y | dist y x < ε }
```

## UniformSpace

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean), lines 195 to 204.

```lean
class UniformSpace (α : Type u) extends TopologicalSpace α where
  /-- The uniformity filter. -/
  protected uniformity : Filter (α × α)
  /-- If `s ∈ uniformity`, then `Prod.swap ⁻¹' s ∈ uniformity`. -/
  protected symm : Tendsto Prod.swap uniformity uniformity
  /-- For every set `u ∈ uniformity`, there exists `v ∈ uniformity` such that `v ○ v ⊆ u`. -/
  protected comp : (uniformity.lift' fun s => s ○ s) ≤ uniformity
  /-- The uniformity agrees with the topology: the neighborhoods filter of each point `x`
  is equal to `Filter.comap (Prod.mk x) (𝓤 α)`. -/
  protected nhds_eq_comap_uniformity (x : α) : 𝓝 x = comap (Prod.mk x) uniformity
```

## UniformSpace.Core

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean), lines 131 to 140.

```lean
structure UniformSpace.Core (α : Type u) where
  /-- The uniformity filter. Once `UniformSpace` is defined, `𝓤 α` (`_root_.uniformity`) becomes the
  normal form. -/
  uniformity : Filter (α × α)
  /-- Every set in the uniformity filter includes the diagonal. -/
  refl : 𝓟 SetRel.id ≤ uniformity
  /-- If `s ∈ uniformity`, then `Prod.swap ⁻¹' s ∈ uniformity`. -/
  symm : Tendsto Prod.swap uniformity uniformity
  /-- For every set `u ∈ uniformity`, there exists `v ∈ uniformity` such that `v ○ v ⊆ u`. -/
  comp : (uniformity.lift' fun s => s ○ s) ≤ uniformity
```

## UniformSpace.Core.toTopologicalSpace

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean), lines 167 to 169.

```lean
def UniformSpace.Core.toTopologicalSpace {α : Type u} (u : UniformSpace.Core α) :
    TopologicalSpace α :=
  .mkOfNhds fun x ↦ .comap (Prod.mk x) u.uniformity
```

## UniformSpace.ofDist

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean), lines 76 to 79.

```lean
def UniformSpace.ofDist (dist : α → α → ℝ) (dist_self : ∀ x : α, dist x x = 0)
    (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z) : UniformSpace α :=
  .ofFun dist dist_self dist_comm dist_triangle ofDist_aux
```

## Nonempty

[Complete pinned source](https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean), lines 839 to 841.

```lean
class inductive Nonempty (α : Sort u) : Prop where
  /-- If `val : α`, then `α` is nonempty. -/
  | intro (val : α) : Nonempty α
```

## Function.Surjective

[Complete pinned source](https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Function.lean), lines 62 to 63.

```lean
def Surjective (f : α → β) : Prop :=
  ∀ b, Exists fun a => f a = b
```

## Compacts

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Sets/Compacts.lean), lines 38 to 41.

```lean
structure Compacts (α : Type*) [TopologicalSpace α] where
  /-- the carrier set, i.e. the points in this set -/
  carrier : Set α
  isCompact' : IsCompact carrier
```

## NonemptyCompacts

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Sets/Compacts.lean), lines 399 to 400.

```lean
structure NonemptyCompacts (α : Type*) [TopologicalSpace α] extends Compacts α where
  nonempty' : carrier.Nonempty
```

## TopologicalSpace.vietoris

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Sets/VietorisTopology.lean), lines 49 to 50.

```lean
protected def vietoris : TopologicalSpace (Set α) :=
  .generateFrom <| powerset '' {U | IsOpen U} ∪ (fun V => {s | (s ∩ V).Nonempty}) '' {V | IsOpen V}
```

## NonemptyCompacts.topology

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Sets/VietorisTopology.lean), lines 825 to 826.

```lean
instance topology : TopologicalSpace (NonemptyCompacts α) :=
  .induced (↑) (.vietoris α)
```

## Composants.IsSubcontinuum

[Complete project source](Foundations.lean) (SHA-256 `34f45c48b5da8ecad8e7503753a67eb819ac56bba683ed909e1003720adc7ab3`), lines 24 to 24.

```lean
def IsSubcontinuum (K : Set X) : Prop := IsCompact K ∧ IsConnected K
```

## Composants.IsIndecomposable

[Complete project source](Foundations.lean) (SHA-256 `34f45c48b5da8ecad8e7503753a67eb819ac56bba683ed909e1003720adc7ab3`), lines 27 to 29.

```lean
def IsIndecomposable (X : Type u) [tX : TopologicalSpace X] : Prop :=
  ∀ K L : Set X, IsSubcontinuum K → IsSubcontinuum L →
    K ∪ L = univ → K = univ ∨ L = univ
```

## Composants.composant

[Complete project source](Foundations.lean) (SHA-256 `34f45c48b5da8ecad8e7503753a67eb819ac56bba683ed909e1003720adc7ab3`), lines 32 to 33.

```lean
def composant (x : X) : Set X :=
  {y | ∃ K : Set X, IsSubcontinuum K ∧ K ≠ univ ∧ x ∈ K ∧ y ∈ K}
```

## Composants.IsOpenCover

[Complete project source](Alexandroff.lean) (SHA-256 `2e7e200ce8eafd86deb934c05a4252594d36f21f63653f376f6895aed374f3f8`), lines 27 to 28.

```lean
def IsOpenCover (ω : Set (Set X)) : Prop :=
  (∀ U ∈ ω, IsOpen U) ∧ ⋃₀ ω = univ
```

## Composants.IsPartitionBetween

[Complete project source](Alexandroff.lean) (SHA-256 `2e7e200ce8eafd86deb934c05a4252594d36f21f63653f376f6895aed374f3f8`), lines 31 to 33.

```lean
def IsPartitionBetween (P A B : Set X) : Prop :=
  IsClosed P ∧ ∃ U V : Set X,
    IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = Pᶜ ∧ A ⊆ U ∧ B ⊆ V
```

## Composants.IsOmegaMap

[Complete project source](Alexandroff.lean) (SHA-256 `2e7e200ce8eafd86deb934c05a4252594d36f21f63653f376f6895aed374f3f8`), lines 36 to 39.

```lean
def IsOmegaMap (ω : Set (Set X)) {P : Set X} {Y : Type v} [_tY : TopologicalSpace Y]
    (f : P → Y) : Prop :=
  Continuous f ∧ ∃ γ : Set (Set Y), IsOpenCover γ ∧
    ∀ V ∈ γ, ∃ U ∈ ω, f ⁻¹' V ⊆ Subtype.val ⁻¹' U
```

## Composants.IsContinuum

[Complete project source](Alexandroff.lean) (SHA-256 `2e7e200ce8eafd86deb934c05a4252594d36f21f63653f376f6895aed374f3f8`), lines 42 to 43.

```lean
def IsContinuum (Y : Type v) [_tY : TopologicalSpace Y] : Prop :=
  Nonempty Y ∧ CompactSpace Y ∧ ConnectedSpace Y ∧ T2Space Y
```

## Disjoint

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Disjoint.lean), lines 48 to 49.

```lean
def Disjoint (a b : α) : Prop :=
  ∀ ⦃x⦄, x ≤ a → x ≤ b → x ≤ ⊥
```

## Set.instCompleteAtomicBooleanAlgebra

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/BooleanAlgebra.lean), lines 32 to 35.

```lean
instance instCompleteAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (Set α) where
  isLUB_sSup _ := ⟨fun s hs _ hx ↦ ⟨s, hs, hx⟩, fun _ h _ ⟨_, ⟨hs, hx⟩⟩ => h hs hx⟩
  isGLB_sInf _ := ⟨fun _ hs _ hx ↦ hx _ hs, fun _ h _ hx _ hs => h hs hx⟩
  iInf_iSup_eq := by intros; ext; simp [Classical.skolem]
```

