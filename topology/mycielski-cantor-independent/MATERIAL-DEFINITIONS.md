# Material imported definitions

Selected: `Mycielski.exists_cantor_independent`.

- `TopologicalSpace`: The supplied topology on X is preserved by compatible metrization; the domain has the standard Cantor product topology.
- `IsOpen`: The open-set predicate of the supplied topology, applied to the localization U and to every binary relation R_n in the actual product topology.
- `IsClosed`: A set whose complement is open; the final Cantor image range is closed in X.
- `closure`: Intersection of all closed supersets; equivalently every neighborhood intersects the original set.
- `Continuous`: Preimages of open sets are open. The final embedding e is continuous; coordinate-splitting homeomorphisms in the proof are continuous in both directions.
- `Homeomorph`: A bijection continuous in both directions, used in the proof to split two distinct product coordinates.
- `TopologicalSpace.induced`: Preimages of codomain opens define the induced topology; closed embedding requires the domain topology to equal it.
- `Filter`: An upward-closed collection of sets containing univ and closed under finite intersections; bottom is allowed until NeBot is supplied.
- `Equiv`: Forward and inverse maps with left and right inverse laws; Homeomorph adds continuity.
- `IsCompact`: Filter compactness, used only for compactness of the Cantor source in the continuous-injective-to-closed-embedding step; ambient X is not assumed compact.
- `CompactSpace`: Compactness of an entire type. The Cantor domain is compact; no compactness premise on X, U or closed metric balls is imposed.
- `Dense`: Every point belongs to the closure of the relation subset in the actual product topology.
- `Set.range`: The set of all image values e(s), with s in the whole Cantor space.
- `PolishSpace`: Second-countable topology and existence of a compatible complete metric; no replacement by a different topology.
- `SecondCountableTopology`: A countable family of sets generates the supplied topology.
- `TopologicalSpace.IsCompletelyMetrizableSpace`: There exists a metric inducing exactly the supplied topology and complete in its uniformity.
- `CompleteSpace`: Every nontrivial Cauchy filter converges in the ambient complete space; an open subspace is not assumed complete.
- `Cauchy`: A nonbottom filter whose product is finer than the uniformity.
- `PerfectSpace`: The universe is preperfect: no point is isolated. The class permits an empty space, but the final nonempty open U supplies nonemptiness.
- `Preperfect`: Every point of the set is an accumulation point of that set.
- `AccPt`: The intersection of the punctured-neighborhood filter and the set filter is nonbottom.
- `Topology.IsInducing`: Domain topology equals the topology induced through the map from the codomain.
- `Topology.IsEmbedding`: An inducing map that is injective.
- `Topology.IsClosedEmbedding`: An inducing injective map whose range is closed. It supplies the actual Cantor copy, not a merely continuous map.

CantorSpace is the fixed Nat→Bool product of discrete Bool spaces. Relations use the actual product X×X; all ordered distinct Cantor points are covered. Nonempty open U prevents empty-space vacuity. PerfectSpace means no isolated points, without a hidden nonemptiness premise. Compatible-complete metrization preserves the given topology, and completeness stays ambient. Closed embedding entails an actual induced-topology injection and closed range.

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L107-L128
```lean
class IsClosed (s : Set X) : Prop where
  /-- The complement of a closed set is an open set. -/
  isOpen_compl : IsOpen sᶜ

/-- A set is clopen if it is both closed and open. -/
def IsClopen (s : Set X) : Prop :=
  IsClosed s ∧ IsOpen s

/--
A set is locally closed if it is the intersection of some open set and some closed set.
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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L112-L128
```lean
def IsClopen (s : Set X) : Prop :=
  IsClosed s ∧ IsOpen s

/--
A set is locally closed if it is the intersection of some open set and some closed set.
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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Defs.lean
SHA256 `4d27914014d20e4b9a6af97ebd7e7bea7451cc37a96dbd102b6d21c9a3f0eb72`

```lean
/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Defs.lean#L42-L50
```lean
/-- Homeomorphism between `X` and `Y`, also called topological isomorphism -/
structure Homeomorph (X : Type*) (Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    extends X ≃ Y where
  /-- The forward map of a homeomorphism is a continuous function. -/
  continuous_toFun : Continuous toFun := by
    first | fun_prop | eta_expand; dsimp; fun_prop | skip
  /-- The inverse map of a homeomorphism is a continuous function. -/
  continuous_invFun : Continuous invFun := by
    first | fun_prop | eta_expand; dsimp; fun_prop | skip
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Defs.lean#L169-L189
```lean
@[simps -isSimp]
instance : Group (X ≃ₜ X) where
  mul f g := g.trans f
  mul_assoc f g h := rfl
  one := .refl X
  one_mul f := rfl
  mul_one f := rfl
  inv := .symm
  inv_mul_cancel := self_trans_symm

@[simp]
theorem one_apply (x : X) : (1 : X ≃ₜ X) x = x := rfl

@[simp]
theorem inv_apply (f : X ≃ₜ X) (x : X) : f⁻¹ x = f.symm x := rfl

@[simp]
theorem mul_apply (f g : X ≃ₜ X) (x : X) : (f * g) x = f (g x) := rfl

protected theorem bijective (h : X ≃ₜ Y) : Function.Bijective h :=
  h.toEquiv.bijective
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Equiv/Defs.lean
SHA256 `c75fb2a102be49010eac04a1602160eaaa2c4c18d12b29bf6f5c45f622dad1e8`

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Equiv/Defs.lean#L62-L77
```lean
universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
structure Equiv (α β : Sort*) where
  /-- The forward map of an equivalence.

  Do NOT use directly. Use the coercion instead. -/
  protected toFun : α → β
  /-- The backward map of an equivalence.

  Do NOT use `e.invFun` directly. Use the coercion of `e.symm` instead. -/
  protected invFun : β → α
  protected left_inv : LeftInverse invFun toFun := by intro; first | rfl | ext <;> rfl
  protected right_inv : RightInverse invFun toFun := by intro; first | rfl | ext <;> rfl
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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean#L128-L135
```lean
/-- A function `f : X → Y` between topological spaces is inducing if the topology on `X` is induced
by the topology on `Y` through `f`, meaning that a set `s : Set X` is open iff it is the preimage
under `f` of some open set `t : Set Y`. -/
@[fun_prop, mk_iff]
structure IsInducing (f : X → Y) : Prop where
  /-- The topology on the domain is equal to the induced topology. -/
  eq_induced : tX = tY.induced f

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean#L144-L150
```lean
/-- A function between topological spaces is an embedding if it is injective,
  and for all `s : Set X`, `s` is open iff it is the preimage of an open set. -/
@[fun_prop, mk_iff]
structure IsEmbedding (f : X → Y) : Prop extends IsInducing f where
  /-- A topological embedding is injective. -/
  injective : Function.Injective f

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean#L157-L162
```lean
/-- A closed embedding is an embedding with closed image. -/
@[fun_prop, mk_iff]
structure IsClosedEmbedding (f : X → Y) : Prop extends IsEmbedding f where
  /-- The range of a closed embedding is a closed set. -/
  isClosed_range : IsClosed <| range f

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L283-L286
```lean
/-- A point `x` is an accumulation point of a filter `F` if `𝓝[≠] x ⊓ F ≠ ⊥`.
See also `ClusterPt`. -/
def AccPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝[≠] x ⊓ F)
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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean
SHA256 `839130eb18758aa2bfcbe3ef40c98fcf9e0827458293fbdb5d04a5ec43b2d08a`

```lean
/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean#L195-L203
```lean
section IsMeagre
open Function TopologicalSpace Set
variable [TopologicalSpace X]

/-- A set is called **nowhere dense** iff its closure has empty interior. -/
def IsNowhereDense (s : Set X) := interior (closure s) = ∅

/-- The empty set is nowhere dense. -/
@[simp]
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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Polish.lean
SHA256 `71c9682ea53f194d1587fbd41695e35cc7fb8f51b1503f695ba4adfb15c52059`

```lean
/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Polish.lean#L56-L64
```lean
/-- A Polish space is a topological space with second countable topology, that can be endowed
with a metric for which it is complete.

To endow a Polish space with a complete metric space structure, do
`letI := upgradeIsCompletelyMetrizable α`.
-/
class PolishSpace (α : Type*) [h : TopologicalSpace α] : Prop
    extends SecondCountableTopology α, IsCompletelyMetrizableSpace α

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean
SHA256 `fbd29cb53487d8ff54efda38cd831d4966a19a052654ef39a09352753986d1d6`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean#L791-L797
```lean
variable (α) in
/-- A second-countable space is one with a countable basis. -/
class _root_.SecondCountableTopology : Prop where
  /-- There exists a countable set of sets that generates the topology. -/
  is_open_generated_countable : ∃ b : Set (Set α), b.Countable ∧ t = TopologicalSpace.generateFrom b

protected theorem IsTopologicalBasis.secondCountableTopology {b : Set (Set α)}
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/CompletelyMetrizable.lean
SHA256 `45e2fe2d79f14e9cf4e87f13f413eef94b418384fc3eaad3dce7b1a730ed54c9`

```lean
/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/CompletelyMetrizable.lean#L150-L157
```lean
/-- A topological space is completely metrizable if there exists a metric space structure
compatible with the topology which makes the space complete.
To endow such a space with a compatible distance, use
`letI := upgradeIsCompletelyMetrizable X`. -/
class IsCompletelyMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  complete : ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧
    @CompleteSpace X m.toUniformSpace

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean
SHA256 `68117051ca85f05bbde595bbbb1dae4b57052c6d3d0fcda3059551b2527874b4`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L368-L373
```lean
/-- A complete space is defined here using uniformities. A uniform space
  is complete if every Cauchy filter converges. -/
@[wikidata Q848569]
class CompleteSpace (α : Type u) [UniformSpace α] : Prop where
  /-- In a complete uniform space, every Cauchy filter converges. -/
  complete : ∀ {f : Filter α}, Cauchy f → ∃ x, f ≤ 𝓝 x
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L27-L33
```lean

/-- A filter `f` is Cauchy if for every entourage `r`, there exists an
  `s ∈ f` such that `s × s ⊆ r`. This is a generalization of Cauchy
  sequences, because if `a : ℕ → α` then the filter of sets containing
  cofinitely many of the `a n` is Cauchy iff `a` is a Cauchy sequence. -/
def Cauchy (f : Filter α) :=
  NeBot f ∧ f ×ˢ f ≤ 𝓤 α
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Perfect.lean
SHA256 `40c4a61f6a8a9f923674520215130f4ffd77ba4f69fb8ee0ba5ed5d461637f7f`

```lean
/-
Copyright (c) 2022 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Perfect.lean#L96-L103
```lean
/--
A topological space `X` is said to be perfect if its universe is a perfect set.
Equivalently, this means that `𝓝[≠] x ≠ ⊥` for every point `x : X`.
-/
@[mk_iff perfectSpace_def]
class PerfectSpace : Prop where
  univ_preperfect : Preperfect (Set.univ : Set α)

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Perfect.lean#L74-L80
```lean

/-- A set `C` is preperfect if all of its points are accumulation points of itself.
If `α` is a T1 space, this is equivalent to the closure of `C` being perfect,
see `preperfect_iff_perfect_closure`. This property is also called dense-in-itself. -/
def Preperfect (C : Set α) : Prop :=
  ∀ x ∈ C, AccPt x (𝓟 C)

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
