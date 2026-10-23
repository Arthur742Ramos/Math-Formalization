# Material imported definitions

The supplied topology, subspace topology, arbitrary subsets, and compatible complete metric retain their literal upstream meanings. Proofs use no separability, closed-domain or uniform-continuity assumption. Challenge and Solution semantic modules compile separately. The local `smallOscillation` and `extensionDomain` definitions are fixed in both entrypoints, with no definition holes. Their literal values and equivalent neighborhood account are compiled in both test modules.

## TopologicalSpace

The supplied open-set topology; all extension conclusions use this same topology.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

The supplied open-set topology; all extension conclusions use this same topology. Literal definitions and dependencies are retained below; semantic bridges compile separately through both entrypoints.

## IsOpen

The open-set predicate of the supplied topology.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

The open-set predicate of the supplied topology. Literal definitions and dependencies are retained below; semantic bridges compile separately through both entrypoints.

## IsClosed

A set whose complement is open; used for closure and Gδ facts.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

A set whose complement is open; used for closure and Gδ facts. Literal definitions and dependencies are retained below; semantic bridges compile separately through both entrypoints.

## closure

Intersection of all closed supersets; equivalently every neighborhood intersects the original set.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

Intersection of all closed supersets; equivalently every neighborhood intersects the original set. Literal definitions and dependencies are retained below; semantic bridges compile separately through both entrypoints.

## Continuous

Preimages of open sets are open; both directions are required by a homeomorphism.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

Preimages of open sets are open; both directions are required by a homeomorphism. Literal definitions and dependencies are retained below; semantic bridges compile separately through both entrypoints.

## Homeomorph

An equivalence with continuous forward and inverse maps. It gives a bijection of the actual subspaces.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

An equivalence with continuous forward and inverse maps. It gives a bijection of the actual subspaces. Literal definitions and dependencies are retained below; semantic bridges compile separately through both entrypoints.

## CompleteSpace

Every nonbottom Cauchy filter converges, for the supplied uniform structure.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

Every nonbottom Cauchy filter converges, for the supplied uniform structure. Literal definitions and dependencies are retained below; semantic bridges compile separately through both entrypoints.

## IsComplete

Every Cauchy filter supported on the set has a limit in that set.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

Every Cauchy filter supported on the set has a limit in that set. Literal definitions and dependencies are retained below; semantic bridges compile separately through both entrypoints.

## MetricSpace

A pseudometric with distance zero implying equality; includes its compatible topology.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

A pseudometric with distance zero implying equality; includes its compatible topology. Literal definitions and dependencies are retained below; semantic bridges compile separately through both entrypoints.

## PseudoMetricSpace

A real-valued distance satisfying pseudometric laws, inducing the inherited uniformity and topology.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

A real-valued distance satisfying pseudometric laws, inducing the inherited uniformity and topology. Literal definitions and dependencies are retained below; semantic bridges compile separately through both entrypoints.

## UniformSpace

An entourage filter with reflexive, symmetric and composition axioms and a compatible topology.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

An entourage filter with reflexive, symmetric and composition axioms and a compatible topology. Literal definitions and dependencies are retained below; semantic bridges compile separately through both entrypoints.

## Cauchy

A nonbottom filter whose product is finer than the entourage filter.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

A nonbottom filter whose product is finer than the entourage filter. Literal definitions and dependencies are retained below; semantic bridges compile separately through both entrypoints.

## Filter.NeBot

A filter is not bottom; this prevents vacuous convergence at points outside the domain closure.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

A filter is not bottom; this prevents vacuous convergence at points outside the domain closure. Literal definitions and dependencies are retained below; semantic bridges compile separately through both entrypoints.

## Filter.Tendsto

The image filter is finer than the target filter, encoding convergence.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

The image filter is finer than the target filter, encoding convergence. Literal definitions and dependencies are retained below; semantic bridges compile separately through both entrypoints.

## nhdsWithin

The neighborhood filter intersected with the principal filter of the set. Only points inside the original set approach the boundary.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

The neighborhood filter intersected with the principal filter of the set. Only points inside the original set approach the boundary. Literal definitions and dependencies are retained below; semantic bridges compile separately through both entrypoints.

## IsGδ

A countable intersection of open sets; a sequence-indexed equivalent form is compiled.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

A countable intersection of open sets; a sequence-indexed equivalent form is compiled. Literal definitions and dependencies are retained below; semantic bridges compile separately through both entrypoints.

## IsCompletelyMetrizableSpace

Existence of a complete metric inducing exactly the supplied topology; no separability requirement.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

Existence of a complete metric inducing exactly the supplied topology; no separability requirement. Literal definitions and dependencies are retained below; semantic bridges compile separately through both entrypoints.

## TopologicalSpace.induced

Preimages of ambient opens define the topology; the subtype instance uses the inclusion.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

Preimages of ambient opens define the topology; the subtype instance uses the inclusion. Literal definitions and dependencies are retained below; semantic bridges compile separately through both entrypoints.

## ContinuousWithinAt

Convergence of f within s at x to f x; expanded through Tendsto, neighborhood and restricted-neighborhood filters.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

Convergence of f within s at x to f x; expanded through Tendsto, neighborhood and restricted-neighborhood filters.

## ContinuousOn

For every point x in s, f converges to f x along neighborhoods restricted to s.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

For every point x in s, f converges to f x along neighborhoods restricted to s.

## Set.MapsTo

Every point of the source set maps into the target set.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

Every point of the source set maps into the target set.

## Set.EqOn

Pointwise equality at every point in the named set.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

Pointwise equality at every point in the named set.

## Set.LeftInvOn

For every point x in s, g (f x) = x; not a global inverse hypothesis.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

For every point x in s, g (f x) = x; not a global inverse hypothesis.

## Filter

An upward-closed collection of sets containing univ and closed under finite intersections; bottom is allowed until NeBot is supplied.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

An upward-closed collection of sets containing univ and closed under finite intersections; bottom is allowed until NeBot is supplied.

## Equiv

Forward and inverse maps with left and right inverse laws; Homeomorph adds continuity.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

Forward and inverse maps with left and right inverse laws; Homeomorph adds continuity.

## extendFrom

Chooses a limit of f along neighborhoods within s if a limit exists. Its arbitrary fallback gives no extension claim without proving convergence and nonbottomness.

Used by: Lavrentieff.extensionDomain_isGδ, Lavrentieff.subset_extensionDomain, Lavrentieff.cauchy_at_extensionDomain, Lavrentieff.continuous_extension, Lavrentieff.isGδ_inter_preimage, Lavrentieff.extend_inverse_maps, Lavrentieff.homeomorph_extension, Lavrentieff.completely_metrizable_extension.

Chooses a limit of f along neighborhoods within s if a limit exists. Its arbitrary fallback gives no extension claim without proving convergence and nonbottomness.

## Mathlib/Topology/Defs/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean

SHA256: `6a16294b9ce69e6f245f45abc59d45db011f2a1c545b4d5d403ccaca5b17c99c`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

### topology-open-closed

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L75-L110

Excerpt SHA256: `32cd02dbee2407d6f2a2709782ad6b65bd88feb3a50558e4951344c640cfafd7`

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

### TopologicalSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L71-L87

Excerpt SHA256: `d0b4bb0467136b0769c0f64a370a326acdea032d7609448a0f7d8337b140031f`

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

### IsClosed

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L107-L109

Excerpt SHA256: `b781df1f94b7e9a0b16791daa67c0bad5d4446809fc5e63093140999f5ae536a`

```lean
class IsClosed (s : Set X) : Prop where
  /-- The complement of a closed set is an open set. -/
  isOpen_compl : IsOpen sᶜ
```

### interior-closure

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L117-L127

Excerpt SHA256: `e08a72b7730b15a59ad60cdbfd00f72b089e1f72279df1dfb1ef9ed8736d0f07`

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

### open-image-Continuous

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L155-L158

Excerpt SHA256: `338d6eb23853e428f3e57edbac5bae462158689cbbd74439f8cfa4cdbfd08e6b`

```lean
structure Continuous (f : X → Y) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
```

## Mathlib/Topology/Order.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean

SHA256: `2705ffc65ea519f775d4e9678578a2dbb18f096325f857c6267ac2bd83af86c5`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

### cantor-Bool-topology

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean#L572-L576

Excerpt SHA256: `2d8bbbaa7265a7f44dd244c394855aa4f2fccb8128ba008672e414bc4393a5d9`

```lean
instance : DiscreteTopology PUnit := ⟨rfl⟩
instance : IndiscreteTopology PUnit := inferInstance

instance : TopologicalSpace Bool := ⊥
instance : DiscreteTopology Bool := ⟨rfl⟩
```

## Mathlib/Topology/Homeomorph/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Defs.lean

SHA256: `4d27914014d20e4b9a6af97ebd7e7bea7451cc37a96dbd102b6d21c9a3f0eb72`

```lean
/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
```

### characterization-Homeomorph

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Defs.lean#L42-L50

Excerpt SHA256: `0b946359899cb78e8004065cc44729b505a4bff977bbf44444b74f5da935a5d4`

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

## Mathlib/Logic/Equiv/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Equiv/Defs.lean

SHA256: `c75fb2a102be49010eac04a1602160eaaa2c4c18d12b29bf6f5c45f622dad1e8`

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
```

### Equiv

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Equiv/Defs.lean#L62-L77

Excerpt SHA256: `c7e7f6bc3d3c61f2670e8d068ee61fd95c4d4affb63eb44970e73def8333fbd0`

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

## Mathlib/Data/Set/Operations.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean

SHA256: `60e5fa9adbd7d068a553d5a28875f5250e0a20771b5179f9f552882d0865c68e`

```lean
/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Johannes Hölzl, Reid Barton, Kim Morrison, Patrick Massot, Kyle Miller,
Minchao Wu, Yury Kudryashov, Floris van Doorn
-/
```

### Set.MapsTo

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean#L291-L295

Excerpt SHA256: `162e4086d78fab50503a79d7134cac004acc4cd1f3551e9027e21b79f571f5b6`

```lean
def EqOn (f₁ f₂ : α → β) (s : Set α) : Prop := ∀ ⦃x⦄, x ∈ s → f₁ x = f₂ x

/-- `MapsTo f s t` means that the image of `s` is contained in `t`. -/
def MapsTo (f : α → β) (s : Set α) (t : Set β) : Prop := ∀ ⦃x⦄, x ∈ s → f x ∈ t

```

### Set.EqOn

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean#L289-L295

Excerpt SHA256: `a8fd02f6a2a8ed8d7f81791cfc6c9a38dc4a3ccab539d8b4d4f5dbdf2520d003`

```lean

/-- Two functions `f₁ f₂ : α → β` are equal on `s` if `f₁ x = f₂ x` for all `x ∈ s`. -/
def EqOn (f₁ f₂ : α → β) (s : Set α) : Prop := ∀ ⦃x⦄, x ∈ s → f₁ x = f₂ x

/-- `MapsTo f s t` means that the image of `s` is contained in `t`. -/
def MapsTo (f : α → β) (s : Set α) (t : Set β) : Prop := ∀ ⦃x⦄, x ∈ s → f x ∈ t

```

### Set.LeftInvOn

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean#L323-L325

Excerpt SHA256: `ae28f2d30ee5732a43d73d7e1ff4874abe37b2078d925383b6a710927bfee8b3`

```lean
/-- `g` is a left inverse to `f` on `s` means that `g (f x) = x` for all `x ∈ s`. -/
def LeftInvOn (g : β → α) (f : α → β) (s : Set α) : Prop := ∀ ⦃x⦄, x ∈ s → g (f x) = x

```

## Mathlib/Topology/Defs/Induced.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean

SHA256: `ba804ff6a2bd28aea83da56dfc339e565745a088d7aeac977643410f1dae8f74`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

### induced

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean#L64-L67

Excerpt SHA256: `878b69c8488a10bac25ce164587ebbe29156ddb4fddd3fe1e9a3911d8bdd8110`

```lean
def induced (f : X → Y) (t : TopologicalSpace Y) : TopologicalSpace X where
  IsOpen s := ∃ t, IsOpen t ∧ f ⁻¹' t = s
  isOpen_univ := ⟨univ, isOpen_univ, preimage_univ⟩
  isOpen_inter := by
```

### subtype-topology

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean#L76-L79

Excerpt SHA256: `eca619b73151480553afac7b4bb4246ad51da55154961c48653ddd5f3074b012`

```lean
instance _root_.instTopologicalSpaceSubtype {p : X → Prop} [t : TopologicalSpace X] :
    TopologicalSpace (Subtype p) :=
  induced (↑) t

```

## Mathlib/Topology/Constructions.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions.lean

SHA256: `47de73fc60746ec4c31fa6e3fcb6d7fe8fbbcf5dbc88c0471fc017040a26467f`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
```

### Pi.product-topology

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions.lean#L66-L68

Excerpt SHA256: `8d6d3bc58b2c45da4e5c3bc1a5c7df8aa12981d05fd20ae4735702d0dcaf5c76`

```lean
instance Pi.topologicalSpace {ι : Type*} {Y : ι → Type v} [t₂ : (i : ι) → TopologicalSpace (Y i)] :
    TopologicalSpace ((i : ι) → Y i) :=
  ⨅ i, induced (fun f => f i) (t₂ i)
```

## Mathlib/Topology/Defs/Filter.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean

SHA256: `3b2ffc8154a531b4f0d3b36aa75ee08635c0df31884ba83baf1b0b0283c13748`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

### nhds

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L127-L134

Excerpt SHA256: `50aa67ca57c8473255d83882eea110cc29269ae9a77d58cae57886b24f0bfa07`

```lean
/-- A set is called a neighborhood of `x` if it contains an open set around `x`. The set of all
neighborhoods of `x` forms a filter, the neighborhood filter at `x`, is here defined as the
infimum over the principal filters of all open sets containing `x`. -/
irreducible_def nhds (x : X) : Filter X :=
  ⨅ s ∈ { s : Set X | x ∈ s ∧ IsOpen s }, 𝓟 s

@[inherit_doc]
scoped[Topology] notation "𝓝" => nhds
```

### cantor-punctured-neighborhood

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L136-L146

Excerpt SHA256: `66d257ee2991366f209610ee7cf88410147833a0310b171216f8690f86f8b42c`

```lean
/-- The "neighborhood within" filter. Elements of `𝓝[s] x` are sets containing the
intersection of `s` and a neighborhood of `x`. -/
def nhdsWithin (x : X) (s : Set X) : Filter X :=
  𝓝 x ⊓ 𝓟 s

@[inherit_doc]
scoped[Topology] notation "𝓝[" s "] " x:100 => nhdsWithin x s

/-- Notation for the filter of punctured neighborhoods of a point. -/
scoped[Topology] notation3 (name := nhdsNE) "𝓝[≠] " x:100 =>
  nhdsWithin x (@singleton _ (Set _) Set.instSingletonSet x)ᶜ
```

### ContinuousWithinAt

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L181-L193

Excerpt SHA256: `b559b9c6ec2686df789143f023caac66842d4aae7639d01f7b2d1a8cd2ae1903`

```lean

/-- A function between topological spaces is continuous at a point `x₀` within a subset `s`
if `f x` tends to `f x₀` when `x` tends to `x₀` while staying within `s`. -/
@[fun_prop]
def ContinuousWithinAt (f : X → Y) (s : Set X) (x : X) : Prop :=
  Tendsto f (𝓝[s] x) (𝓝 (f x))

/-- A function between topological spaces is continuous on a subset `s`
when it's continuous at every point of `s` within `s`. -/
@[fun_prop]
def ContinuousOn (f : X → Y) (s : Set X) : Prop :=
  ∀ x ∈ s, ContinuousWithinAt f s x

```

### ContinuousOn

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L185-L193

Excerpt SHA256: `d9663d656828a101e1408462bb7e9e30362c2bdacfd315f14aea87f55317ec76`

```lean
def ContinuousWithinAt (f : X → Y) (s : Set X) (x : X) : Prop :=
  Tendsto f (𝓝[s] x) (𝓝 (f x))

/-- A function between topological spaces is continuous on a subset `s`
when it's continuous at every point of `s` within `s`. -/
@[fun_prop]
def ContinuousOn (f : X → Y) (s : Set X) : Prop :=
  ∀ x ∈ s, ContinuousWithinAt f s x

```

### neighborhood-definition

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L127-L140

Excerpt SHA256: `99cbf9d30e8e3a988d770d038915bdfe686faef04548cc4979fa883f27699359`

```lean
/-- A set is called a neighborhood of `x` if it contains an open set around `x`. The set of all
neighborhoods of `x` forms a filter, the neighborhood filter at `x`, is here defined as the
infimum over the principal filters of all open sets containing `x`. -/
irreducible_def nhds (x : X) : Filter X :=
  ⨅ s ∈ { s : Set X | x ∈ s ∧ IsOpen s }, 𝓟 s

@[inherit_doc]
scoped[Topology] notation "𝓝" => nhds

/-- The "neighborhood within" filter. Elements of `𝓝[s] x` are sets containing the
intersection of `s` and a neighborhood of `x`. -/
def nhdsWithin (x : X) (s : Set X) : Filter X :=
  𝓝 x ⊓ 𝓟 s

```

## Mathlib/Order/Filter/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Basic.lean

SHA256: `5dac9f84ef61915588e250fbb6e816ecf3d3183a94aa7e31f85e390baeb30afb`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
```

### Filter.le_principal_iff

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Basic.lean#L365-L367

Excerpt SHA256: `d08e61a69841f2db9a4d86aa848cc71575f01b48205811c4cb5515695f163896`

```lean
@[simp]
theorem le_principal_iff {s : Set α} {f : Filter α} : f ≤ 𝓟 s ↔ s ∈ f :=
  ⟨fun h => h Subset.rfl, fun hs _ ht => mem_of_superset hs ht⟩
```

## Mathlib/Order/Filter/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean

SHA256: `d0b1e4022a3910b2768e8786a3a66d701db0cb4c59c055b3bd17ec4cd28a60e5`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
```

### Filter.principal

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L147-L158

Excerpt SHA256: `b9ac7078f265922dbe9c103f5320642c8b0341f855d674b959a051d39edcee33`

```lean
/-- The principal filter of `s` is the collection of all supersets of `s`. -/
def principal (s : Set α) : Filter α where
  sets := { t | s ⊆ t }
  univ_sets := subset_univ s
  sets_of_superset hx := Subset.trans hx
  inter_sets := subset_inter

@[inherit_doc]
scoped notation "𝓟" => Filter.principal

@[simp] theorem mem_principal : s ∈ 𝓟 t ↔ t ⊆ s := Iff.rfl

```

### Filter

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L71-L83

Excerpt SHA256: `0d537bbb0e92a3e5a1c9a1c33b713a8c1351c8f23d9b835133dba47b1c526200`

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

### Filter.order

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L183-L190

Excerpt SHA256: `a99ab18fd794b2e2b76c56bfa8532bcb16e403417f304a87285b776cb5782aca`

```lean
  le f g := ∀ ⦃U : Set α⦄, U ∈ g → U ∈ f
  le_antisymm a b h₁ h₂ := filter_eq <| Subset.antisymm h₂ h₁
  le_refl a := Subset.rfl
  le_trans a b c h₁ h₂ := Subset.trans h₂ h₁

theorem le_def : f ≤ g ↔ ∀ x ∈ g, x ∈ f :=
  Iff.rfl

```

### Filter.product

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L444-L452

Excerpt SHA256: `9ef3719fef82cd6404287f98980c3054bbce035b372a7bd938e80fccdc056a78`

```lean
/-- Product of filters. This is the filter generated by Cartesian products
of elements of the component filters. -/
instance instSProd : SProd (Filter α) (Filter β) (Filter (α × β)) where
  sprod f g := f.comap Prod.fst ⊓ g.comap Prod.snd

theorem prod_eq_inf (f : Filter α) (g : Filter β) : f ×ˢ g = f.comap Prod.fst ⊓ g.comap Prod.snd :=
  rfl

/-- The product of an indexed family of filters. -/
```

### Filter.map-Tendsto

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L405-L423

Excerpt SHA256: `e6f89a53ff1df261c7705955e27a8d227354e5926f369e20b02c35ad98be4313`

```lean

/-- Unexpander printing `Filter.EventuallySubset l s t` as `s ≤ᶠ[l] t`. -/
@[app_unexpander Filter.EventuallySubset]
meta def unexpandEventuallySubset : Lean.PrettyPrinter.Unexpander
  | `($_ $l $s $t) => `($s ≤ᶠ[$l] $t)
  | _ => throw ()

/-- The forward map of a filter -/
def map (m : α → β) (f : Filter α) : Filter β where
  sets := preimage m ⁻¹' f.sets
  univ_sets := univ_mem
  sets_of_superset hs st := mem_of_superset hs fun _x hx ↦ st hx
  inter_sets hs ht := inter_mem hs ht

/-- `Filter.Tendsto` is the generic "limit of a function" predicate.
  `Tendsto f l₁ l₂` asserts that for every `l₂` neighborhood `a`,
  the `f`-preimage of `a` is an `l₁` neighborhood. -/
def Tendsto (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.map f ≤ l₂
```

### Filter.comap

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L425-L439

Excerpt SHA256: `362366ce36802bc59b3b10b58727f2c6636d06fcf2d31241e21f8d26a375d782`

```lean
/-- The inverse map of a filter. A set `s` belongs to `Filter.comap m f` if either of the following
equivalent conditions hold.

1. There exists a set `t ∈ f` such that `m ⁻¹' t ⊆ s`. This is used as a definition.
2. The set `kernImage m s = {y | ∀ x, m x = y → x ∈ s}` belongs to `f`, see `Filter.mem_comap'`.
3. The set `(m '' sᶜ)ᶜ` belongs to `f`, see `Filter.mem_comap_iff_compl` and
   `Filter.compl_mem_comap`.
-/
def comap (m : α → β) (f : Filter β) : Filter α where
  sets := { s | ∃ t ∈ f, m ⁻¹' t ⊆ s }
  univ_sets := ⟨univ, univ_mem, subset_univ _⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' ∩ b', inter_mem ha₁ hb₁, inter_subset_inter ha₂ hb₂⟩

```

### Filter.NeBot

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L268-L277

Excerpt SHA256: `1488e11444dcb443471e0955a43cd486caed1add58d2970214794e265e2b9627`

```lean
/-- A filter is `NeBot` if it is not equal to `⊥`, or equivalently the empty set does not belong to
the filter. Bourbaki include this assumption in the definition of a filter but we prefer to have a
`CompleteLattice` structure on `Filter _`, so we use a typeclass argument in lemmas instead. -/
class NeBot (f : Filter α) : Prop where
  /-- The filter is nontrivial: `f ≠ ⊥` or equivalently, `∅ ∉ f`. -/
  ne' : f ≠ ⊥

@[push ←]
theorem neBot_iff {f : Filter α} : NeBot f ↔ f ≠ ⊥ :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
```

### cantor-NeBot

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L267-L277

Excerpt SHA256: `de28aba95e4d9fbf3ff965f6b2efbc6b1591d5b15e59c8422eefe58ba95c15ad`

```lean

/-- A filter is `NeBot` if it is not equal to `⊥`, or equivalently the empty set does not belong to
the filter. Bourbaki include this assumption in the definition of a filter but we prefer to have a
`CompleteLattice` structure on `Filter _`, so we use a typeclass argument in lemmas instead. -/
class NeBot (f : Filter α) : Prop where
  /-- The filter is nontrivial: `f ≠ ⊥` or equivalently, `∅ ∉ f`. -/
  ne' : f ≠ ⊥

@[push ←]
theorem neBot_iff {f : Filter α} : NeBot f ↔ f ≠ ⊥ :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
```

## Mathlib/Topology/UniformSpace/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean

SHA256: `0678d9754b2f7c95f4ca1c62ff0fe923bfff83092e890b26d524040be1f1a47c`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
```

### UniformSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean#L185-L209

Excerpt SHA256: `a67f56908a4cffd4c4c069fff92e9f5256c8d56e81e6c5e074c827feac86bc13`

```lean
-- the topological structure is embedded in the uniform structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].
/-- A uniform space is a generalization of the "uniform" topological aspects of a
  metric space. It consists of a filter on `α × α` called the "uniformity", which
  satisfies properties analogous to the reflexivity, symmetry, and triangle properties
  of a metric.

  A metric space has a natural uniformity, and a uniform space has a natural topology.
  A topological group also has a natural uniformity, even when it is not metrizable. -/
@[wikidata Q652446]
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

/-- The uniformity is a filter on α × α (inferred from an ambient uniform space
  structure on α). -/
def uniformity (α : Type u) [UniformSpace α] : Filter (α × α) :=
  @UniformSpace.uniformity α _
```

### UniformSpace.Core

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean#L129-L140

Excerpt SHA256: `5313987700fb612d91a82f7603e0ae3fe6cda1b5d64773c26afedb74c7f1bb37`

```lean
/-- This core description of a uniform space is outside of the type class hierarchy. It is useful
  for constructions of uniform spaces, when the topology is derived from the uniform space. -/
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

## Mathlib/Topology/Neighborhoods.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Neighborhoods.lean

SHA256: `ef0e4d65986641366ffcc380a613f210207fee31e8640e1488a8cae41395383a`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

### mem_nhds_iff

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Neighborhoods.lean#L64-L66

Excerpt SHA256: `3920d4125f26e7f74ea0eb050f41fa4c4f00ef056b57524cd6b93066efb1d515`

```lean
theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t :=
  (nhds_basis_opens x).mem_iff.trans <| exists_congr fun _ =>
    ⟨fun h => ⟨h.2, h.1.2, h.1.1⟩, fun h => ⟨⟨h.2.2, h.2.1⟩, h.1⟩⟩
```

## Mathlib/Topology/MetricSpace/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Defs.lean

SHA256: `cc1f7ad1c82dc79235c23718b6915211d4707a9e6e5bc68ee78ec85f024c45d9`

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

### MetricSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Defs.lean#L54-L71

Excerpt SHA256: `5b56d60557f748a59780862ed4ee67767eb50c1e00b5a5ca2fde9be6cdd68c7e`

```lean
/-- A metric space is a type endowed with a `ℝ`-valued distance `dist` satisfying
`dist x y = 0 ↔ x = y`, commutativity `dist x y = dist y x`, and the triangle inequality
`dist x z ≤ dist x y + dist y z`.

See pseudometric spaces (`PseudoMetricSpace`) for the similar class with the `dist x y = 0 ↔ x = y`
assumption weakened to `dist x x = 0`.

Any metric space is a T1 topological space and a uniform space (see `TopologicalSpace`, `T1Space`,
`UniformSpace`), where the topology and uniformity come from the metric.

We make the uniformity/topology part of the data instead of deriving it from the metric.
This e.g. ensures that we do not get a diamond when doing
`[MetricSpace α] [MetricSpace β] : TopologicalSpace (α × β)`:
The product metric and product topology agree, but not definitionally so.
See Note [forgetful inheritance]. -/
@[wikidata Q180953]
class MetricSpace (α : Type u) : Type u extends PseudoMetricSpace α where
  eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y
```

## Mathlib/Topology/MetricSpace/Pseudo/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean

SHA256: `13cd9bc80e44bf7b61a55b5b1c2993058ac995f8803a6fb58c230c23a1d0fa35`

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

### Dist

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L100-L108

Excerpt SHA256: `db01a57fd9285c10d2dfa5a5015cf57d0ac68b497028b697181e603289d9fc04`

```lean

/-- The distance function (given an ambient metric space on `α`), which returns
a real number `dist x y` given `x y : α`. This type class does not enforce non-negativity. -/
@[ext]
class Dist (α : Type*) where
  /-- Distance between two points -/
  dist : α → α → ℝ

export Dist (dist)
```

### PseudoMetricSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L124-L153

Excerpt SHA256: `a0d4f299a39e8aa7ba8f7db608e624ed07b23dc5de029b5215d6bed2274daca4`

```lean
set_option backward.privateInPublic.warn false in
/-- A pseudometric space is a type endowed with a `ℝ`-valued distance `dist` satisfying
reflexivity `dist x x = 0`, commutativity `dist x y = dist y x`, and the triangle inequality
`dist x z ≤ dist x y + dist y z`.

Note that we do not require `dist x y = 0 → x = y`. See metric spaces (`MetricSpace`) for the
similar class with that stronger assumption.

Any pseudometric space is a topological space and a uniform space (see `TopologicalSpace`,
`UniformSpace`), where the topology and uniformity come from the metric.
Note that a T1 pseudometric space is just a metric space.

We make the uniformity/topology part of the data instead of deriving it from the metric. This e.g.
ensures that we do not get a diamond when doing
`[PseudoMetricSpace α] [PseudoMetricSpace β] : TopologicalSpace (α × β)`:
The product metric and product topology agree, but not definitionally so.
See Note [forgetful inheritance]. -/
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

### Metric.isOpen_iff

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L833-L841

Excerpt SHA256: `2cb15902c148b72cec105db174db8b3cf474f25885869836b8f9bcc319bcc105`

```lean
    (𝓝 x).HasBasis (fun _ => True) fun n : ℕ => closedBall x (r ^ n) :=
  nhds_basis_uniformity (uniformity_basis_dist_le_pow h0 h1)

theorem isOpen_iff : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ball x ε ⊆ s := by
  simp only [isOpen_iff_mem_nhds, mem_nhds_iff]

@[simp] theorem isOpen_ball : IsOpen (ball x ε) :=
  isOpen_iff.2 fun _ => exists_ball_subset_ball

```

### Metric.isBounded_iff

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L625-L629

Excerpt SHA256: `7dd22941d9b0880008d4085c57ff057daf39d91cab6f6076cfe9ef2873a5eaae`

```lean
theorem isBounded_iff {s : Set α} :
    IsBounded s ↔ ∃ C : ℝ, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C := by
  rw [isBounded_def, ← Filter.mem_sets, @PseudoMetricSpace.cobounded_sets α, mem_ofPred_eq,
    compl_compl]

```

## Mathlib/Topology/MetricSpace/Pseudo/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean

SHA256: `7a5c0bd0f454d486cc09454bb647a3757d209154f1481c7947b061b0548e5e3f`

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

### Metric.cauchy_iff

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean#L164-L166

Excerpt SHA256: `e6cc78652991cda1494893c83d58219bb9ed712be0d32b10a0a7cfb2f655d56f`

```lean
protected theorem cauchy_iff {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ ε > 0, ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, dist x y < ε :=
  uniformity_basis_dist.cauchy_iff
```

## Mathlib/Topology/MetricSpace/Cauchy.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Cauchy.lean

SHA256: `9bf8322a49ceef3280008db0b63b21befc5d1c3581e55c7d043ad25f4ae47618`

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

### Metric.cauchySeq_iff

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Cauchy.lean#L53-L61

Excerpt SHA256: `150c559bcbe82b9fde277b6d5bf85fa2ce930c41c31f2d101102126879018242`

```lean
section CauchySeq

variable [Nonempty β] [SemilatticeSup β]

/-- In a pseudometric space, Cauchy sequences are characterized by the fact that, eventually,
the distance between its elements is arbitrarily small -/
theorem Metric.cauchySeq_iff {u : β → α} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  uniformity_basis_dist.cauchySeq_iff
```

## Mathlib/Topology/UniformSpace/Cauchy.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean

SHA256: `68117051ca85f05bbde595bbbb1dae4b57052c6d3d0fcda3059551b2527874b4`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

### Cauchy

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L27-L33

Excerpt SHA256: `093fba2cb6e2058042cdafb8d2367864e3fec7907ad47cc9288a6509d2c35cc5`

```lean

/-- A filter `f` is Cauchy if for every entourage `r`, there exists an
  `s ∈ f` such that `s × s ⊆ r`. This is a generalization of Cauchy
  sequences, because if `a : ℕ → α` then the filter of sets containing
  cofinitely many of the `a n` is Cauchy iff `a` is a Cauchy sequence. -/
def Cauchy (f : Filter α) :=
  NeBot f ∧ f ×ˢ f ≤ 𝓤 α
```

### IsComplete

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L35-L38

Excerpt SHA256: `856f9594a85679ec2725c2c1cfbfe75680d84a66edb8b33aefec8716ba18dd43`

```lean
/-- A set `s` is called *complete*, if any Cauchy filter `f` such that `s ∈ f`
has a limit in `s` (formally, it satisfies `f ≤ 𝓝 x` for some `x ∈ s`). -/
def IsComplete (s : Set α) :=
  ∀ f, Cauchy f → f ≤ 𝓟 s → ∃ x ∈ s, f ≤ 𝓝 x
```

### CompleteSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L368-L373

Excerpt SHA256: `11cb273661eccc126e169d1905a8f37fd8f8d051d7118fa067f22b116b366c75`

```lean
/-- A complete space is defined here using uniformities. A uniform space
  is complete if every Cauchy filter converges. -/
@[wikidata Q848569]
class CompleteSpace (α : Type u) [UniformSpace α] : Prop where
  /-- In a complete uniform space, every Cauchy filter converges. -/
  complete : ∀ {f : Filter α}, Cauchy f → ∃ x, f ≤ 𝓝 x
```

### completeSpace_iff_isComplete_univ

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L407-L412

Excerpt SHA256: `7dd91310d3eccf779c254b58ca90f4f73cf856307fd3ad0894021c9ef38077e1`

```lean
/-- If `univ` is complete, the space is a complete space -/
theorem completeSpace_of_isComplete_univ (h : IsComplete (univ : Set α)) : CompleteSpace α :=
  ⟨fun hf => let ⟨x, _, hx⟩ := h _ hf ((@principal_univ α).symm ▸ le_top); ⟨x, hx⟩⟩

theorem completeSpace_iff_isComplete_univ : CompleteSpace α ↔ IsComplete (univ : Set α) :=
  ⟨@isComplete_univ α _, completeSpace_of_isComplete_univ⟩
```

### cauchy_iff

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L47-L53

Excerpt SHA256: `ec670cce44cc90cc9a0d2d516d49bd8f446fe316c14d6dae67921cbc3a4849ae`

```lean
theorem cauchy_iff' {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ s ∈ 𝓤 α, ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, (x, y) ∈ s :=
  (𝓤 α).basis_sets.cauchy_iff

theorem cauchy_iff {f : Filter α} : Cauchy f ↔ NeBot f ∧ ∀ s ∈ 𝓤 α, ∃ t ∈ f, t ×ˢ t ⊆ s :=
  cauchy_iff'.trans <| by
    simp only [subset_def, Prod.forall, mem_prod_eq, and_imp, forall_mem_comm]
```

## Mathlib/Order/Filter/Prod.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Prod.lean

SHA256: `2aa26b2b6beb3860fe1584961fe9f87d22c4d9cf7e719c6817a97c90dc244367`

```lean
/-
Copyright (c) 2022 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Yury Kudryashov, Kevin H. Wilson, Heather Macbeth
-/
```

### Filter.mem_prod_iff

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Prod.lean#L52-L59

Excerpt SHA256: `55010dac263ead057dd2f09e496453866685af85abe7b22563b86eeeef24656c`

```lean
theorem mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : Filter β} :
    s ∈ f ×ˢ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ ×ˢ t₂ ⊆ s := by
  constructor
  · rintro ⟨t₁, ⟨s₁, hs₁, hts₁⟩, t₂, ⟨s₂, hs₂, hts₂⟩, rfl⟩
    exact ⟨s₁, hs₁, s₂, hs₂, fun p ⟨h, h'⟩ => ⟨hts₁ h, hts₂ h'⟩⟩
  · rintro ⟨t₁, ht₁, t₂, ht₂, h⟩
    exact mem_inf_of_inter (preimage_mem_comap ht₁) (preimage_mem_comap ht₂) h

```

## Mathlib/Order/Filter/Tendsto.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Tendsto.lean

SHA256: `76800f92ca0414bd4f31e94719ac9cac2985bd2b083035380c3e32111e0405ce`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
```

### Filter.tendsto_def

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Tendsto.lean#L31-L33

Excerpt SHA256: `4c72dad4fe0238b5b998a3fbccd5b7f7095b1f6ff3b2d1495b3ab7566d8f0d00`

```lean
theorem tendsto_def {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ :=
  Iff.rfl
```

## Mathlib/Order/Filter/AtTopBot/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/AtTopBot/Defs.lean

SHA256: `4091e8e0921cd9c2d70511ea017f5d9bdf861a9bc3e4408eb8625c81c1f6b621`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
```

### Filter.atTop

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/AtTopBot/Defs.lean#L29-L40

Excerpt SHA256: `0414b8d5164f9dab4515dade24e8985b274e6226b91ba6e843fbbdd78d40d59b`

```lean

/-- `atTop` is the filter representing the limit `→ ∞` on an ordered set.
It is generated by the collection of up-sets `{b | a ≤ b}`.
(The preorder need not have a top element for this to be well defined,
and indeed is trivial when a top element `x` exists, i.e., it coincides with `pure x`.) -/
@[to_dual
/-- `atBot` is the filter representing the limit `→ -∞` on an ordered set.
It is generated by the collection of down-sets `{b | b ≤ a}`.
(The preorder need not have a bottom element for this to be well defined,
and indeed is trivial when a bottom element `x` exists, i.e., it coincides with `pure x`.) -/]
def atTop [Preorder α] : Filter α :=
  ⨅ a, 𝓟 (Ici a)
```

## Mathlib/Topology/Bornology/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bornology/Basic.lean

SHA256: `427d7eff3bd67d3b8a3ba2df3636786b248405f789871161145d274f929d466e`

```lean
/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
```

### Bornology

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bornology/Basic.lean#L48-L55

Excerpt SHA256: `6b90100aad31395953206030fe496a5a526e9db1473af7893d4213fc9d139bd8`

```lean
/-- A **bornology** on a type `α` is a filter of cobounded sets which contains the cofinite filter.
Such spaces are equivalently specified by their bounded sets, see `Bornology.ofBounded`
and `Bornology.ext_iff_isBounded` -/
class Bornology (α : Type*) where
  /-- The filter of cobounded sets in a bornology. -/
  cobounded (α) : Filter α
  /-- The cobounded filter in a bornology is smaller than the cofinite filter. -/
  le_cofinite (α) : cobounded ≤ cofinite
```

## Mathlib/Topology/MetricSpace/Bounded.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Bounded.lean

SHA256: `dbdb5dce531767c8e6b56f004d9d3a4cde9173a5a11ef40733a86cb432cadd2b`

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
```

### Metric.nonempty_iInter_of_nonempty_biInter

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Bounded.lean#L564-L570

Excerpt SHA256: `17aa72fea3bce982cdc3613292981d760ee2ed9bbb705423938181d1d451ec18`

```lean
/-- In a complete space, if a family of closed sets with diameter tending to `0` is such that each
finite intersection is nonempty, then the total intersection is also nonempty. -/
theorem nonempty_iInter_of_nonempty_biInter [CompleteSpace α] {s : ℕ → Set α}
    (hs : ∀ n, IsClosed (s n)) (h's : ∀ n, IsBounded (s n)) (h : ∀ N, (⋂ n ≤ N, s n).Nonempty)
    (h' : Tendsto (fun n => diam (s n)) atTop (𝓝 0)) : (⋂ n, s n).Nonempty :=
  (hs 0).isComplete.nonempty_iInter_of_nonempty_biInter hs h's h h'

```

## Mathlib/Topology/GDelta/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean

SHA256: `839130eb18758aa2bfcbe3ef40c98fcf9e0827458293fbdb5d04a5ec43b2d08a`

```lean
/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
```

### IsGδ

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean#L62-L64

Excerpt SHA256: `7e136567a7e24bfece5698ef37f33eb8f5cefd4a7610ba8f35c4f9e765917187`

```lean
/-- A Gδ set is a countable intersection of open sets. -/
def IsGδ (s : Set X) : Prop :=
  ∃ T : Set (Set X), (∀ t ∈ T, IsOpen t) ∧ T.Countable ∧ s = ⋂₀ T
```

### isGδ_iff_eq_iInter_nat

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean#L90-L101

Excerpt SHA256: `0e2113073e8539401f878584cd5a9c865b112b247a20ffa4506d3acdf6118a1e`

```lean
lemma isGδ_iff_eq_iInter_nat {s : Set X} :
    IsGδ s ↔ ∃ (f : ℕ → Set X), (∀ n, IsOpen (f n)) ∧ s = ⋂ n, f n := by
  refine ⟨?_, ?_⟩
  · rintro ⟨T, hT, T_count, rfl⟩
    rcases Set.eq_empty_or_nonempty T with rfl | hT
    · exact ⟨fun _n ↦ univ, fun _n ↦ isOpen_univ, by simp⟩
    · obtain ⟨f, hf⟩ : ∃ (f : ℕ → Set X), T = range f := Countable.exists_eq_range T_count hT
      exact ⟨f, by simp_all, by simp [hf]⟩
  · rintro ⟨f, hf, rfl⟩
    exact .iInter_of_isOpen hf

alias ⟨IsGδ.eq_iInter_nat, _⟩ := isGδ_iff_eq_iInter_nat
```

## Mathlib/Topology/Metrizable/CompletelyMetrizable.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/CompletelyMetrizable.lean

SHA256: `45e2fe2d79f14e9cf4e87f13f413eef94b418384fc3eaad3dce7b1a730ed54c9`

```lean
/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
```

### IsCompletelyMetrizableSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/CompletelyMetrizable.lean#L154-L156

Excerpt SHA256: `b3d0593275db87c4c9e59e149d56341f6f3e4ec372a4e857cd945bd4adc1fe34`

```lean
class IsCompletelyMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  complete : ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧
    @CompleteSpace X m.toUniformSpace
```

### compatible-complete-metric

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/CompletelyMetrizable.lean#L191-L211

Excerpt SHA256: `20644352ac64e08eda5aff19295568ff9379aa8a2327cc5b165d1e4d36c4f61e`

```lean
noncomputable def completelyMetrizableMetric (X : Type*) [TopologicalSpace X]
    [h : IsCompletelyMetrizableSpace X] : MetricSpace X :=
  h.complete.choose.replaceTopology h.complete.choose_spec.1.symm

theorem complete_completelyMetrizableMetric (X : Type*) [ht : TopologicalSpace X]
    [h : IsCompletelyMetrizableSpace X] :
    @CompleteSpace X (completelyMetrizableMetric X).toUniformSpace := by
  convert! h.complete.choose_spec.2
  exact MetricSpace.replaceTopology_eq _ _

/-- This definition endows a completely metrizable space with a complete metric. Use it as:
`letI := upgradeIsCompletelyMetrizable X`. -/
@[instance_reducible]
noncomputable
def upgradeIsCompletelyMetrizable (X : Type*) [TopologicalSpace X] [IsCompletelyMetrizableSpace X] :
    UpgradedIsCompletelyMetrizableSpace X :=
  letI := completelyMetrizableMetric X
  { complete_completelyMetrizableMetric X with }

namespace IsCompletelyMetrizableSpace

```

### closed-embedding-complete-transfer

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/CompletelyMetrizable.lean#L247-L258

Excerpt SHA256: `a405119d196e6c10ed92a3f8136a02a065dffbef5fdadc464328d486299eef59`

```lean
/-- Given a closed embedding into a completely metrizable space,
the source space is also completely metrizable. -/
theorem _root_.Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace [TopologicalSpace X]
    [TopologicalSpace Y] [IsCompletelyMetrizableSpace Y] {f : X → Y} (hf : IsClosedEmbedding f) :
    IsCompletelyMetrizableSpace X := by
  let := upgradeIsCompletelyMetrizable Y
  let : MetricSpace X := hf.isEmbedding.comapMetricSpace f
  have : CompleteSpace X := by
    rw [completeSpace_iff_isComplete_range hf.isEmbedding.to_isometry.isUniformInducing]
    exact hf.isClosed_range.isComplete
  infer_instance

```

### countable-product-complete-metrizable

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/CompletelyMetrizable.lean#L219-L225

Excerpt SHA256: `e01c850ec60d05d2a8fbf0fb7cc98abfdf02f2da78519e2f4cb64dac32590fac`

```lean
/-- A countable product of completely metrizable spaces is completely metrizable. -/
instance pi_countable {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, IsCompletelyMetrizableSpace (X i)] : IsCompletelyMetrizableSpace (Π i, X i) := by
  let := fun i ↦ upgradeIsCompletelyMetrizable (X i)
  infer_instance

/-- A disjoint union of completely metrizable spaces is completely metrizable. -/
```

### closed-subset-complete-metrizable

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/CompletelyMetrizable.lean#L293-L297

Excerpt SHA256: `8761f5d7e2575d916c778523a8b909f61aff21ec02823dcd2ea6e12403e74023`

```lean
/-- A closed subset of a completely metrizable space is also completely metrizable. -/
theorem _root_.IsClosed.isCompletelyMetrizableSpace
    [TopologicalSpace X] [IsCompletelyMetrizableSpace X]
    {s : Set X} (hs : IsClosed s) : IsCompletelyMetrizableSpace s :=
  hs.isClosedEmbedding_subtypeVal.IsCompletelyMetrizableSpace
```

## Mathlib/Topology/ExtendFrom.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/ExtendFrom.lean

SHA256: `04db674bf9430b1c11e2766ee532cd4645d2ba5208c3fda5ebcf9e315c6fa522`

```lean
/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Anatole Dedecker
-/
```

### extendFrom

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/ExtendFrom.lean#L40-L46

Excerpt SHA256: `ddc31257955ad85d87e7cc8a9ab7eeee41a058645aed224f95c522d6bf7ee9c5`

```lean
then `g x₀` is defined to be one of these `y`. Else, `g x₀` could be anything. -/
def extendFrom (A : Set X) (f : X → Y) : X → Y :=
  fun x ↦ @limUnder _ _ _ ⟨f x⟩ (𝓝[A] x) f

/-- If `f` converges to some `y` as `x` tends to `x₀` within `A`,
then `f` tends to `extendFrom A f x` as `x` tends to `x₀`. -/
theorem tendsto_extendFrom {A : Set X} {f : X → Y} {x : X} (h : ∃ y, Tendsto f (𝓝[A] x) (𝓝 y)) :
```


### extendFrom-guarantees

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/ExtendFrom.lean#L44-L79

Excerpt SHA256: `7a92b6bf512aa79c9de9094dad9ddd25e5606a985c0c2e980474c255dd96be4b`

```lean
/-- If `f` converges to some `y` as `x` tends to `x₀` within `A`,
then `f` tends to `extendFrom A f x` as `x` tends to `x₀`. -/
theorem tendsto_extendFrom {A : Set X} {f : X → Y} {x : X} (h : ∃ y, Tendsto f (𝓝[A] x) (𝓝 y)) :
    Tendsto f (𝓝[A] x) (𝓝 <| extendFrom A f x) :=
  tendsto_nhds_limUnder h

theorem extendFrom_eq [T2Space Y] {A : Set X} {f : X → Y} {x : X} {y : Y} (hx : x ∈ closure A)
    (hf : Tendsto f (𝓝[A] x) (𝓝 y)) : extendFrom A f x = y :=
  haveI := mem_closure_iff_nhdsWithin_neBot.mp hx
  tendsto_nhds_unique (tendsto_nhds_limUnder ⟨y, hf⟩) hf

theorem extendFrom_extends [T2Space Y] {f : X → Y} {A : Set X} (hf : ContinuousOn f A) :
    ∀ x ∈ A, extendFrom A f x = f x :=
  fun x x_in ↦ extendFrom_eq (subset_closure x_in) (hf x x_in)

/-- If `f` is a function to a T₃ space `Y` which has a limit within `A` at any
point of a set `B ⊆ closure A`, then `extendFrom A f` is continuous on `B`. -/
theorem continuousOn_extendFrom [RegularSpace Y] {f : X → Y} {A B : Set X} (hB : B ⊆ closure A)
    (hf : ∀ x ∈ B, ∃ y, Tendsto f (𝓝[A] x) (𝓝 y)) : ContinuousOn (extendFrom A f) B := by
  set φ := extendFrom A f
  intro x x_in
  suffices ∀ V' ∈ 𝓝 (φ x), IsClosed V' → φ ⁻¹' V' ∈ 𝓝[B] x by
    simpa [ContinuousWithinAt, (closed_nhds_basis (φ x)).tendsto_right_iff]
  intro V' V'_in V'_closed
  obtain ⟨V, V_in, V_op, hV⟩ : ∃ V ∈ 𝓝 x, IsOpen V ∧ V ∩ A ⊆ f ⁻¹' V' := by
    have := tendsto_extendFrom (hf x x_in)
    rcases (nhdsWithin_basis_open x A).tendsto_left_iff.mp this V' V'_in with ⟨V, ⟨hxV, V_op⟩, hV⟩
    exact ⟨V, IsOpen.mem_nhds V_op hxV, V_op, hV⟩
  suffices ∀ y ∈ V ∩ B, φ y ∈ V' from
    mem_of_superset (inter_mem_inf V_in <| mem_principal_self B) this
  rintro y ⟨hyV, hyB⟩
  have := mem_closure_iff_nhdsWithin_neBot.mp (hB hyB)
  have limy : Tendsto f (𝓝[A] y) (𝓝 <| φ y) := tendsto_extendFrom (hf y hyB)
  have hVy : V ∈ 𝓝 y := IsOpen.mem_nhds V_op hyV
  have : V ∩ A ∈ 𝓝[A] y := by simpa only [inter_comm] using inter_mem_nhdsWithin A hVy
  exact V'_closed.mem_of_tendsto limy (mem_of_superset this hV)
```

The raw definition calls limUnder. The retained tendsto_extendFrom, extendFrom_eq, extendFrom_extends and continuousOn_extendFrom theorems prove its choice-independent semantics under existence of limits, closure/nonbottomness, Hausdorff uniqueness and regularity. continuous_extension supplies precisely these hypotheses, rather than assuming this helper extends arbitrary maps.
