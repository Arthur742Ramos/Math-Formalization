# Material imported definitions

Selected: WeakMinimal.surjective_of_weakMixing, WeakMinimal.hitting_thick, WeakMinimal.minimal_hitting_syndetic, WeakMinimal.thick_meets_syndetic, WeakMinimal.weakMixing_minimal_product.

Compact Hausdorff surjectivity, inclusive hitting thickness/syndeticity and actual heterogeneous product transitivity. No metric, invertibility or hidden onto premise; Y need not be Hausdorff. Independent review owns completeness.

- `TopologicalSpace`: Actual supplied open-set topology; actual binary product is infimum of the two projection-induced topologies.
- `IsOpen`: Open in the supplied topology; target preimages and actual product rectangles are open.
- `IsClosed`: Complement open in supplied topology; the continuous compact image is closed in Hausdorff X.
- `closure`: Intersection of closed supersets in the supplied topology; used for image density/closed image surjectivity.
- `Continuous`: All open preimages are open. Both f and g continuous; compactness and density supply no inverse continuity.
- `TopologicalSpace.induced`: Inverse-image topology along a projection; actual heterogeneous product, not a box or assumed rectangle topology.
- `Filter`: Literal pinned filter/neighborhood dependency of compactness and closure; no additional hypothesis beyond the displayed compactness/topology contracts.
- `IsCompact`: Every nonbottom filter on the set has a cluster point there; used via the finite open-subcover theorem, not metric sequential compactness.
- `CompactSpace`: The whole supplied space is compact; finite open preimage subcovers produce a uniform bound in Y, and compact image closure is used for surjectivity in X.
- `Dense`: Every ambient point lies in closure of the set. Minimality quantifies density of every actual natural orbit, with all starts included.
- `Set.range`: Existential image of every natural time or domain point; orbit density and image-surjectivity use literal ranges.
- `Finset`: Finite constraint indices and compact subcover indices, including finite sup to bound gaps.
- `Nat.iterate`: Natural zero is identity and successor applies the same map. Actual iterates obey additive composition; all product coordinates share one time.
- `ClusterPt`: Nonbottom intersection of the actual neighborhood filter and given filter; compactness cluster point, not deleted-neighborhood accumulation.
- `T2Space`: Distinct X points have disjoint open neighborhoods, and compact subsets of X are closed. No T2 hypothesis on Y.
- `Filter.principal`: Filter containing exactly supersets of the given set; compactness quantifies filters concentrated on that set.
- `Filter.NeBot`: Filter differs from bottom, equivalently excludes the empty set; compactness quantifies nontrivial filters.

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean
SHA256 `6a16294b9ce69e6f245f45abc59d45db011f2a1c545b4d5d403ccaca5b17c99c`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L75-L110
```lean
  protected IsOpen : Set X → Prop
  /-- The set representing the whole space is an open set.
  Use `isOpen_univ` in the root namespace instead. -/
  protected isOpen_univ : IsOpen univ
  /-- The intersection of two open sets is an open set. Use `IsOpen.inter` instead. -/
  protected isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  /-- The union of a family of open sets is an open set.
  Use `isOpen_sUnion` in the root namespace instead. -/
  protected isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)

variable {X : Type u} {Y : Type v}

/-! ### Predicates on sets -/

section Defs

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

/-- `IsOpen s` means that `s` is open in the ambient topological space on `X` -/
@[wikidata Q213363]
def IsOpen : Set X → Prop := TopologicalSpace.IsOpen

@[simp] theorem isOpen_univ : IsOpen (univ : Set X) := TopologicalSpace.isOpen_univ

theorem IsOpen.inter (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) :=
  TopologicalSpace.isOpen_inter s t hs ht

theorem isOpen_sUnion {s : Set (Set X)} (h : ∀ t ∈ s, IsOpen t) : IsOpen (⋃₀ s) :=
  TopologicalSpace.isOpen_sUnion s h

/-- A set is closed if its complement is open -/
@[wikidata Q320357]
class IsClosed (s : Set X) : Prop where
  /-- The complement of a closed set is an open set. -/
  isOpen_compl : IsOpen sᶜ

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L71-L87
```lean
/-- A topology on `X`. -/
@[to_dual_dont_translate]
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

variable {X : Type u} {Y : Type v}

/-! ### Predicates on sets -/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L107-L109
```lean
class IsClosed (s : Set X) : Prop where
  /-- The complement of a closed set is an open set. -/
  isOpen_compl : IsOpen sᶜ
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L117-L127
```lean
Also see `isLocallyClosed_tfae` and other lemmas in `Mathlib/Topology/LocallyClosed.lean`.
-/
def IsLocallyClosed (s : Set X) : Prop := ∃ (U Z : Set X), IsOpen U ∧ IsClosed Z ∧ s = U ∩ Z

/-- The interior of a set `s` is the largest open subset of `s`. -/
def interior (s : Set X) : Set X :=
  ⋃₀ { t | IsOpen t ∧ t ⊆ s }

/-- The closure of `s` is the smallest closed set containing `s`. -/
def closure (s : Set X) : Set X :=
  ⋂₀ { t | IsClosed t ∧ s ⊆ t }
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L155-L158
```lean
structure Continuous (f : X → Y) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L142-L151
```lean
def coborder (s : Set X) : Set X :=
  (closure s \ s)ᶜ

/-- A set is dense in a topological space if every point belongs to its closure. -/
def Dense (s : Set X) : Prop :=
  ∀ x, x ∈ closure s

/-- `f : α → X` has dense range if its range (image) is a dense subset of `X`. -/
def DenseRange {α : Type*} (f : α → X) := Dense (range f)

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean
SHA256 `2705ffc65ea519f775d4e9678578a2dbb18f096325f857c6267ac2bd83af86c5`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean#L572-L576
```lean
instance : DiscreteTopology PUnit := ⟨rfl⟩
instance : IndiscreteTopology PUnit := inferInstance

instance : TopologicalSpace Bool := ⊥
instance : DiscreteTopology Bool := ⟨rfl⟩
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean
SHA256 `ba804ff6a2bd28aea83da56dfc339e565745a088d7aeac977643410f1dae8f74`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean#L64-L67
```lean
def induced (f : X → Y) (t : TopologicalSpace Y) : TopologicalSpace X where
  IsOpen s := ∃ t, IsOpen t ∧ f ⁻¹' t = s
  isOpen_univ := ⟨univ, isOpen_univ, preimage_univ⟩
  isOpen_inter := by
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean#L76-L79
```lean
instance _root_.instTopologicalSpaceSubtype {p : X → Prop} [t : TopologicalSpace X] :
    TopologicalSpace (Subtype p) :=
  induced (↑) t

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions.lean
SHA256 `47de73fc60746ec4c31fa6e3fcb6d7fe8fbbcf5dbc88c0471fc017040a26467f`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions.lean#L66-L68
```lean
instance Pi.topologicalSpace {ι : Type*} {Y : ι → Type v} [t₂ : (i : ι) → TopologicalSpace (Y i)] :
    TopologicalSpace ((i : ι) → Y i) :=
  ⨅ i, induced (fun f => f i) (t₂ i)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean
SHA256 `3b2ffc8154a531b4f0d3b36aa75ee08635c0df31884ba83baf1b0b0283c13748`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L280-L303
```lean
def MapClusterPt {ι : Type*} (x : X) (F : Filter ι) (u : ι → X) : Prop :=
  ClusterPt x (map u F)

/-- A point `x` is an accumulation point of a filter `F` if `𝓝[≠] x ⊓ F ≠ ⊥`.
See also `ClusterPt`. -/
def AccPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝[≠] x ⊓ F)

/-- A set `s` is compact if for every nontrivial filter `f` that contains `s`,
there exists `a ∈ s` such that every set of `f` meets every neighborhood of `a`. -/
def IsCompact (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f

variable (X) in
/-- Type class for compact spaces. Separation is sometimes included in the definition, especially
in the French literature, but we do not include it here. -/
@[wikidata Q381892]
class CompactSpace : Prop where
  /-- In a compact space, `Set.univ` is a compact set. -/
  isCompact_univ : IsCompact (Set.univ : Set X)

variable (X) in
/-- `X` is a noncompact topological space if it is not a compact space. -/
class NoncompactSpace : Prop where
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L280-L303
```lean
def MapClusterPt {ι : Type*} (x : X) (F : Filter ι) (u : ι → X) : Prop :=
  ClusterPt x (map u F)

/-- A point `x` is an accumulation point of a filter `F` if `𝓝[≠] x ⊓ F ≠ ⊥`.
See also `ClusterPt`. -/
def AccPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝[≠] x ⊓ F)

/-- A set `s` is compact if for every nontrivial filter `f` that contains `s`,
there exists `a ∈ s` such that every set of `f` meets every neighborhood of `a`. -/
def IsCompact (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f

variable (X) in
/-- Type class for compact spaces. Separation is sometimes included in the definition, especially
in the French literature, but we do not include it here. -/
@[wikidata Q381892]
class CompactSpace : Prop where
  /-- In a compact space, `Set.univ` is a compact set. -/
  isCompact_univ : IsCompact (Set.univ : Set X)

variable (X) in
/-- `X` is a noncompact topological space if it is not a compact space. -/
class NoncompactSpace : Prop where
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L275-L276
```lean
def ClusterPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝 x ⊓ F)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L275-L276
```lean
def ClusterPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝 x ⊓ F)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L126-L131
```lean

/-- A set is called a neighborhood of `x` if it contains an open set around `x`. The set of all
neighborhoods of `x` forms a filter, the neighborhood filter at `x`, is here defined as the
infimum over the principal filters of all open sets containing `x`. -/
irreducible_def nhds (x : X) : Filter X :=
  ⨅ s ∈ { s : Set X | x ∈ s ∧ IsOpen s }, 𝓟 s
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean
SHA256 `d0b1e4022a3910b2768e8786a3a66d701db0cb4c59c055b3bd17ec4cd28a60e5`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L71-L83
```lean
/-- A filter `F` on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. We do not forbid this collection to be
all sets of `α`. -/
@[to_dual_dont_translate]
structure Filter (α : Type*) where
  /-- The set of sets that belong to the filter. -/
  sets : Set (Set α)
  /-- The set `Set.univ` belongs to any filter. -/
  univ_sets : Set.univ ∈ sets
  /-- If a set belongs to a filter, then its superset belongs to the filter as well. -/
  sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets
  /-- If two sets belong to a filter, then their intersection belongs to the filter as well. -/
  inter_sets {x y} : x ∈ sets → y ∈ sets → x ∩ y ∈ sets
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L147-L152
```lean
/-- The principal filter of `s` is the collection of all supersets of `s`. -/
def principal (s : Set α) : Filter α where
  sets := { t | s ⊆ t }
  univ_sets := subset_univ s
  sets_of_superset hx := Subset.trans hx
  inter_sets := subset_inter
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L268-L273
```lean
/-- A filter is `NeBot` if it is not equal to `⊥`, or equivalently the empty set does not belong to
the filter. Bourbaki include this assumption in the definition of a filter but we prefer to have a
`CompleteLattice` structure on `Filter _`, so we use a typeclass argument in lemmas instead. -/
class NeBot (f : Filter α) : Prop where
  /-- The filter is nontrivial: `f ≠ ⊥` or equivalently, `∅ ∉ f`. -/
  ne' : f ≠ ⊥
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean
SHA256 `60e5fa9adbd7d068a553d5a28875f5250e0a20771b5179f9f552882d0865c68e`

```lean
/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Johannes Hölzl, Reid Barton, Kim Morrison, Patrick Massot, Kyle Miller,
Minchao Wu, Yury Kudryashov, Floris van Doorn
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean#L170-L174
```lean

This function is more flexible than `f '' univ`, as the image requires that the domain is in Type
and not an arbitrary Sort. -/
def range (f : ι → α) : Set α := {x | ∃ y, f y = x}

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Defs.lean
SHA256 `ac132a546c19ca9e9ec46f864faae346c2c613c8bd7123bb0807c4ad630c302d`

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Finset/Defs.lean#L75-L79
```lean
structure Finset (α : Type*) where
  /-- The underlying multiset -/
  val : Multiset α
  /-- `val` contains no duplicates -/
  nodup : Nodup val
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Function/Iterate.lean
SHA256 `bf42e948bbf3fae276cd05b8e53d1d143feec96f95d81675bee103010e210339`

```lean
/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Function/Iterate.lean#L41-L43
```lean
def Nat.iterate {α : Sort u} (op : α → α) : ℕ → α → α
  | 0, a => a
  | succ k, a => iterate op k (op a)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Lindelof.lean
SHA256 `e75a097a0ac483a700c8eb13d91246dd151d3e34edf331f8fcb4f4f15fbe505d`

```lean
/-
Copyright (c) 2023 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Lindelof.lean#L51-L52
```lean
def IsLindelof (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f] [CountableInterFilter f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Lindelof.lean#L292-L296
```lean
theorem isLindelof_iff_countable_subcover :
    IsLindelof s ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) → ∃ t : Set ι, t.Countable ∧ s ⊆ ⋃ i ∈ t, U i :=
  ⟨fun hs ↦ hs.elim_countable_subcover, isLindelof_of_countable_subcover⟩

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/Hausdorff.lean
SHA256 `95c58f7ad7ef3ea627d5af8d2427c7d7e08a47207ed084e51945217f32566f06`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/Hausdorff.lean#L81-L91
```lean
/-- A T₂ space, also known as a Hausdorff space, is one in which for every
  `x ≠ y` there exists disjoint open sets around `x` and `y`. This is
  the most widely used of the separation axioms. -/
@[mk_iff]
class T2Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Every two points in a Hausdorff space admit disjoint open neighbourhoods. -/
  t2 : Pairwise fun x y => ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v

/-- Two different points can be separated by open sets. -/
theorem t2_separation [T2Space X] {x y : X} (h : x ≠ y) :
    ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v :=
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions/SumProd.lean
SHA256 `35d6365bebe8c5d331fe01289e857ccc81e6f6392b1f01835d834a35a6931666`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions/SumProd.lean#L53-L55
```lean
instance instTopologicalSpaceProd [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y] :
    TopologicalSpace (X × Y) :=
  induced Prod.fst t₁ ⊓ induced Prod.snd t₂
```
