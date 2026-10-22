# Material imported definitions: open Baire representation

Exact-pin material Mathlib definitions for the six open Baire representation contracts. Core Function.Surjective and type Nonempty are separately retained in verification/core-imported-definitions.json. This is an independently assembled bounded semantic inventory; actual bridge compilation, transitive axioms, protected export comparison, kernels, exact-commit canonical receipts and editorial/registry decisions are separate.

The principal domain is the product topology on natural-number sequences with each coordinate discrete. No fixed Baire metric is added to its statement. The local OpenScheme structure records real construction obligations rather than assuming openness of the desired map. Its fields and the definition of OpenScheme.limit are visible in OpenBaire.lean and independently reviewed.

## TopologicalSpace

A topology is an open-set predicate closed under univ, finite intersections and arbitrary unions.

Every open, closure, continuous and open-map assertion uses the supplied topology. In the metric versions its compatibility is recorded by the metric/uniformity fields; the Polish version uses an equal compatible complete metric, not a new topology.

Selected uses: `OpenBaire.exists_open_refinement`, `OpenBaire.exists_open_scheme`, `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## IsOpen

The open-set predicate of the ambient topology.

The refinement sets and all scheme nodes are genuinely open. Exact cylinder-image equality, together with the product cylinder basis, yields openness of the limit map on arbitrary opens.

Selected uses: `OpenBaire.exists_open_refinement`, `OpenBaire.exists_open_scheme`, `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## closure

The intersection of all closed supersets of a set.

Closure-child containment is stronger than child containment; it ensures the complete-space branch limit remains inside every parent open set. The construction bounds closure of a small ball by a larger ball contained in the parent.

Selected uses: `OpenBaire.exists_open_refinement`, `OpenBaire.exists_open_scheme`, `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## IsClosed

A set is closed when its complement is open.

Used to interpret closure as the smallest closed superset, not an assumption that the open scheme sets are themselves closed. No compactness of closed balls is used.

Selected uses: `OpenBaire.exists_open_refinement`, `OpenBaire.exists_open_scheme`, `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## Set.Nonempty

There exists an element belonging to the set.

Every open node is nonempty. The refinement lemma explicitly assumes a nonempty parent, so countable covers can be enumerated by all naturals using repetitions; no empty child or empty index is silently introduced.

Selected uses: `OpenBaire.exists_open_refinement`, `OpenBaire.exists_open_scheme`, `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## MetricSpace

A real-valued pseudometric separating points, with stored compatible uniformity and topology.

Distance separation gives uniqueness of branch intersections. Small open balls refine arbitrary opens. No boundedness, compactness, properness or no-isolated-points assumption is present.

Selected uses: `OpenBaire.exists_open_refinement`, `OpenBaire.exists_open_scheme`, `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## PseudoMetricSpace

Symmetric real-valued distance with reflexivity and triangle inequality, plus compatible extended distance, uniformity, topology and bornology.

The fields edist_dist and uniformity_dist identify the extended diameter and filter completeness with the real metric. The actual selected metric is separating because MetricSpace extends this class.

Selected uses: `OpenBaire.exists_open_refinement`, `OpenBaire.exists_open_scheme`, `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## UniformSpace

A uniformity filter on pairs with symmetry and composition, compatible with the stored topology through neighborhood comaps.

CompleteSpace is stated for this uniformity. Compatibility with the metric and topology is essential: the limit is convergence for the original topology, not for an unrelated uniformity.

Selected uses: `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## CompleteSpace

Every Cauchy filter converges to a point of the space.

Upstream CantorScheme proves totality using Cauchy sequences selected from nested nonempty nodes. The local proof then proves uniqueness via vanishing diameters. The refinement and scheme-construction lemmas do not assume completeness.

Selected uses: `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## Cauchy

A nontrivial filter whose product with itself is below the uniformity.

This is the filter definition underlying CompleteSpace. In the inherited metric uniformity it agrees with the usual eventually arbitrarily close criterion, as witnessed by retained metric bridges.

Selected uses: `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## CauchySeq

The filter image of atTop under a sequence is a Cauchy filter.

The full sequence of chosen points along each branch is Cauchy; totality does not merely find a convergent subsequence.

Selected uses: `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## IsComplete

Every Cauchy filter supported by the set has a limit in that set.

Whole-space completeness is equivalent to completeness of univ; it is not completeness of every open scheme node for a subspace metric.

Selected uses: `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## Filter.Tendsto

The image filter of the source is below the target filter.

VanishingDiam concerns the entire sequence of extended diameters along each branch tending to zero, indexed by natural-number atTop and the extended-nonnegative-real neighborhood filter.

Selected uses: `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## Metric.ball

The set of points at real distance strictly less than the radius from a center.

Refinement balls have positive radius min(delta/2,epsilon/2). Their closures stay in the parent open set, and their extended diameters are bounded by epsilon.

Selected uses: `OpenBaire.exists_open_refinement`, `OpenBaire.exists_open_scheme`, `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## Metric.closedBall

The set of points at real distance at most the radius from a center.

Only closure(ball) subset closedBall and a strict radius comparison are used. No equality closure(ball)=closedBall and no compact-ball assumption is needed.

Selected uses: `OpenBaire.exists_open_refinement`, `OpenBaire.exists_open_scheme`, `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## Metric.ediam

The supremum of extended distances between every pair of points in the set.

The bound ediam(V)<=ofReal(epsilon) is an extended-real bound on all pairs. It does not use real diameter, whose infinity convention would be unsuitable. Geometric bounds imply VanishingDiam.

Selected uses: `OpenBaire.exists_open_refinement`, `OpenBaire.exists_open_scheme`, `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## Countable

A type admits an injective function into the naturals.

The selected countable subcover is nonempty, allowing a surjection from naturals onto its subtype. Repetitions are permitted; finite covers need not be inflated by empty sets.

Selected uses: `OpenBaire.exists_open_refinement`, `OpenBaire.exists_open_scheme`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## Set.Countable

The subtype induced by the set is countable.

Applies to a chosen set of cover indices, not to the underlying Polish space. The ambient space may be uncountable.

Selected uses: `OpenBaire.exists_open_refinement`, `OpenBaire.exists_open_scheme`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## SecondCountableTopology

The topology is generated by a countable family of subsets.

A proved countable-basis equivalence justifies countable-basis language. The open-union countable-subcover theorem supplies each refinement cover; second countability is not required by the generic cylinder-image theorem once an OpenScheme is supplied.

Selected uses: `OpenBaire.exists_open_refinement`, `OpenBaire.exists_open_scheme`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## IsTopologicalBasis

A family of opens that refines every open neighborhood at each of its points.

The actual basis used is PiNat.isTopologicalBasis_cylinders for the product of discrete naturals. Openness of every cylinder image extends to openness of all open-set images.

Selected uses: `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## IsCompletelyMetrizableSpace

There exists a metric giving exactly the supplied topology whose induced uniformity is complete.

upgradeIsCompletelyMetrizable chooses such a metric while preserving the TopologicalSpace instance. An arbitrary pre-existing compatible metric need not be complete.

Selected uses: `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## PolishSpace

The supplied topology is second-countable and admits a compatible complete metric.

This is the mixin extending SecondCountableTopology and IsCompletelyMetrizableSpace. It does not exclude the empty space; explicit Nonempty is required for an image of the inhabited Baire space.

Selected uses: `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## Continuous

The preimage of every open codomain set is open in the domain.

The domain has the product topology of discrete naturals. Upstream VanishingDiam.map_continuous is composed with the total-domain inclusion; continuity is not inferred from surjectivity or openness.

Selected uses: `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## IsOpenMap

The image of every open domain set is open in the codomain.

This is an independent conjunct, established from exact cylinder images. It is stronger than continuity, which concerns preimages, and no injectivity or closed-map property is asserted.

Selected uses: `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## Set.image

An element belongs to the image when it is the value of the function at some element of the domain set.

The image_cylinder theorem proves literal equality with the corresponding scheme open set, both inclusions. The reverse inclusion extends the prescribed finite prefix through any prescribed target point.

Selected uses: `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## Set.preimage

The set of points whose function value belongs to the target set.

This occurs in the literal continuity predicate. It is distinct from image and no interchange of arbitrary intersections and images is assumed.

Selected uses: `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## Set.range

The image of the universal domain set.

Surjectivity follows from image_cylinder at level zero, whose domain cylinder and corresponding scheme root are both univ.

Selected uses: `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## TopologicalSpace.induced

A set is open for the induced topology precisely when it is the preimage of an open set under the defining function.

The product topology on Baire space is the infimum of the topologies induced by each coordinate evaluation. The source coordinates use the canonical discrete topology on naturals. The partial induced-map subtype also uses the induced topology before totality is proved.

Selected uses: `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## PiNat.cylinder

Sequences agreeing with the given sequence in every coordinate strictly below n.

The product cylinder uses all coordinates less than n, including the empty prefix at zero. It is not a binary path model.

Selected uses: `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## PiNat.res

The first n coordinates recorded as a reversed finite list.

res x (n+1)=x n :: res x n; the newest coordinate is prepended. The branch extension and scheme-child convention match this order exactly.

Selected uses: `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## CantorScheme.inducedMap

A partial branch map whose domain consists of branches with nonempty intersection and whose value is a chosen intersection point.

The local limit is the same map after totality has been proved; it is not a choice of arbitrary cluster points. Membership is in every open node on that branch.

Selected uses: `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## CantorScheme.ClosureAntitone

The closure of each child set is contained in its parent set.

Stronger than ordinary antitonicity; supplies actual open-node membership of the complete-space limit, not just closure membership.

Selected uses: `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## CantorScheme.VanishingDiam

On every infinite branch, extended diameters of its finite-prefix sets tend to zero.

The constructed bound is ofReal((1/2)^length) at every positive depth. The root need not be bounded. Completeness and nonempty nodes imply totality; vanishing diameter also implies continuity.

Selected uses: `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## ENNReal.ofReal

A real converted to the extended nonnegative reals by truncating negative values to zero.

All requested refinement radii epsilon are strictly positive; all geometric diameter bounds are positive. No infinity-to-zero real-diameter conversion occurs.

Selected uses: `OpenBaire.exists_open_refinement`, `OpenBaire.exists_open_scheme`, `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## DiscreteTopology

The given topology equals the discrete topology, so every subset is open.

Each natural-number coordinate has the canonical TopologicalSpace Nat = bottom and DiscreteTopology Nat instance. The product uses Pi.topologicalSpace, not the discrete topology on all sequences. Cylinders, rather than single sequences, form the domain basis.

Selected uses: `OpenBaire.OpenScheme.image_cylinder`, `OpenBaire.exists_continuous_open_surjective_of_completeSpace`, `OpenBaire.exists_continuous_open_surjective`, `OpenBaire.exists_continuous_open_surjective_iff_nonempty`.

## Pinned source: Mathlib/Topology/Defs/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean

SHA256: 6a16294b9ce69e6f245f45abc59d45db011f2a1c545b4d5d403ccaca5b17c99c

Git blob SHA1: 326105821a5a8ce5041ccf8dce22779bd55fa923

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/

```

### topology-open-closed

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L75-L110

Excerpt SHA256: 32cd02dbee2407d6f2a2709782ad6b65bd88feb3a50558e4951344c640cfafd7

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

### interior-closure

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L117-L127

Excerpt SHA256: e08a72b7730b15a59ad60cdbfd00f72b089e1f72279df1dfb1ef9ed8736d0f07

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

### TopologicalSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L71-L87

Excerpt SHA256: d0b4bb0467136b0769c0f64a370a326acdea032d7609448a0f7d8337b140031f

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

Excerpt SHA256: b781df1f94b7e9a0b16791daa67c0bad5d4446809fc5e63093140999f5ae536a

```lean
class IsClosed (s : Set X) : Prop where
  /-- The complement of a closed set is an open set. -/
  isOpen_compl : IsOpen sᶜ

```

### open-image-Continuous

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L155-L158

Excerpt SHA256: 338d6eb23853e428f3e57edbac5bae462158689cbbd74439f8cfa4cdbfd08e6b

```lean
structure Continuous (f : X → Y) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)

```

### open-image-IsOpenMap

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L162-L162

Excerpt SHA256: d91c92444f2b971290b93ffd23a6416423dac73dd3e1109c8369af7f8dff0dac

```lean
def IsOpenMap (f : X → Y) : Prop := ∀ U : Set X, IsOpen U → IsOpen (f '' U)

```

## Pinned source: Mathlib/Data/Set/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean

SHA256: 4b5433ba90d229d2875756f2c486de41e2e1b5be89b7255be5fe7ed2e0c524c7

Git blob SHA1: 866ef6ab673f737a4ffbb7b2138402d5c76e6c05

```lean
/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

```

### Set.Nonempty

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L277-L281

Excerpt SHA256: cb3870fa0008d18792a7122276c41e3e45998a2f2defae575b4225f0a2cf53de

```lean
/-- The property `s.Nonempty` expresses the fact that the set `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def Nonempty (s : Set α) : Prop :=
  ∃ x, x ∈ s

```

### open-image-Set.image

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L266-L266

Excerpt SHA256: 33bdb2da05833cc25b82686d5f94a98b24778577e5407ac386d980dd33e609a4

```lean
def image {β : Type v} (f : α → β) (s : Set α) : Set β := {f a | a ∈ s}

```

## Pinned source: Mathlib/Topology/MetricSpace/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Defs.lean

SHA256: cc1f7ad1c82dc79235c23718b6915211d4707a9e6e5bc68ee78ec85f024c45d9

Git blob SHA1: 10910c95e518dfacb8d4fcb88d7e689315791952

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/

```

### MetricSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Defs.lean#L54-L71

Excerpt SHA256: 5b56d60557f748a59780862ed4ee67767eb50c1e00b5a5ca2fde9be6cdd68c7e

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

## Pinned source: Mathlib/Topology/MetricSpace/Pseudo/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean

SHA256: 13cd9bc80e44bf7b61a55b5b1c2993058ac995f8803a6fb58c230c23a1d0fa35

Git blob SHA1: 912bc464320d8ea70f002255c59e9f79d41f6ac2

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/

```

### Dist

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L100-L108

Excerpt SHA256: db01a57fd9285c10d2dfa5a5015cf57d0ac68b497028b697181e603289d9fc04

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

Excerpt SHA256: a0d4f299a39e8aa7ba8f7db608e624ed07b23dc5de029b5215d6bed2274daca4

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

### Metric.ball

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L368-L375

Excerpt SHA256: 9254e95110ac29f8ddd4f9c3efd54b1c170b0977361801dc39aa766eb7cdf894

```lean
/-- `ball x ε` is the set of all points `y` with `dist y x < ε` -/
@[wikidata Q838611]
def ball (x : α) (ε : ℝ) : Set α :=
  { y | dist y x < ε }

@[simp]
theorem mem_ball : y ∈ ball x ε ↔ dist y x < ε :=
  Iff.rfl

```

### Metric.closedBall

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L420-L426

Excerpt SHA256: 3597e1d083a212916773e453633c64a0db15ad8d09df6e8af009aa33b3babd61

```lean
/-- `closedBall x ε` is the set of all points `y` with `dist y x ≤ ε` -/
def closedBall (x : α) (ε : ℝ) :=
  { y | dist y x ≤ ε }

@[simp] theorem mem_closedBall : y ∈ closedBall x ε ↔ dist y x ≤ ε := Iff.rfl

theorem mem_closedBall' : y ∈ closedBall x ε ↔ dist x y ≤ ε := by rw [dist_comm, mem_closedBall]

```

### Metric.isBounded_iff

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L625-L629

Excerpt SHA256: 7dd22941d9b0880008d4085c57ff057daf39d91cab6f6076cfe9ef2873a5eaae

```lean
theorem isBounded_iff {s : Set α} :
    IsBounded s ↔ ∃ C : ℝ, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C := by
  rw [isBounded_def, ← Filter.mem_sets, @PseudoMetricSpace.cobounded_sets α, mem_ofPred_eq,
    compl_compl]


```

### Metric.isOpen_iff

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean#L833-L841

Excerpt SHA256: 2cb15902c148b72cec105db174db8b3cf474f25885869836b8f9bcc319bcc105

```lean
    (𝓝 x).HasBasis (fun _ => True) fun n : ℕ => closedBall x (r ^ n) :=
  nhds_basis_uniformity (uniformity_basis_dist_le_pow h0 h1)

theorem isOpen_iff : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ball x ε ⊆ s := by
  simp only [isOpen_iff_mem_nhds, mem_nhds_iff]

@[simp] theorem isOpen_ball : IsOpen (ball x ε) :=
  isOpen_iff.2 fun _ => exists_ball_subset_ball


```

## Pinned source: Mathlib/Topology/MetricSpace/Pseudo/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean

SHA256: 7a5c0bd0f454d486cc09454bb647a3757d209154f1481c7947b061b0548e5e3f

Git blob SHA1: c2269f217cc1266e8d378b9493c90e1480a0c438

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/

```

### Metric.cauchy_iff

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean#L164-L166

Excerpt SHA256: e6cc78652991cda1494893c83d58219bb9ed712be0d32b10a0a7cfb2f655d56f

```lean
protected theorem cauchy_iff {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ ε > 0, ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, dist x y < ε :=
  uniformity_basis_dist.cauchy_iff

```

## Pinned source: Mathlib/Topology/MetricSpace/Cauchy.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Cauchy.lean

SHA256: 9bf8322a49ceef3280008db0b63b21befc5d1c3581e55c7d043ad25f4ae47618

Git blob SHA1: 4f65c04a3aac9896699e53b84846de79031d9836

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/

```

### Metric.cauchySeq_iff

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Cauchy.lean#L53-L61

Excerpt SHA256: 150c559bcbe82b9fde277b6d5bf85fa2ce930c41c31f2d101102126879018242

```lean
section CauchySeq

variable [Nonempty β] [SemilatticeSup β]

/-- In a pseudometric space, Cauchy sequences are characterized by the fact that, eventually,
the distance between its elements is arbitrarily small -/
theorem Metric.cauchySeq_iff {u : β → α} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  uniformity_basis_dist.cauchySeq_iff

```

## Pinned source: Mathlib/Topology/UniformSpace/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean

SHA256: 0678d9754b2f7c95f4ca1c62ff0fe923bfff83092e890b26d524040be1f1a47c

Git blob SHA1: 3f068a41cafe8605be201dd24b3843bcbba45a6e

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/

```

### UniformSpace.Core

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean#L129-L140

Excerpt SHA256: 5313987700fb612d91a82f7603e0ae3fe6cda1b5d64773c26afedb74c7f1bb37

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

### UniformSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean#L185-L209

Excerpt SHA256: a67f56908a4cffd4c4c069fff92e9f5256c8d56e81e6c5e074c827feac86bc13

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

## Pinned source: Mathlib/Topology/UniformSpace/Cauchy.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean

SHA256: 68117051ca85f05bbde595bbbb1dae4b57052c6d3d0fcda3059551b2527874b4

Git blob SHA1: 86640c96b74c3a4161ecae8151f0cdec46f6d64c

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/

```

### Cauchy

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L27-L33

Excerpt SHA256: 093fba2cb6e2058042cdafb8d2367864e3fec7907ad47cc9288a6509d2c35cc5

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

Excerpt SHA256: 856f9594a85679ec2725c2c1cfbfe75680d84a66edb8b33aefec8716ba18dd43

```lean
/-- A set `s` is called *complete*, if any Cauchy filter `f` such that `s ∈ f`
has a limit in `s` (formally, it satisfies `f ≤ 𝓝 x` for some `x ∈ s`). -/
def IsComplete (s : Set α) :=
  ∀ f, Cauchy f → f ≤ 𝓟 s → ∃ x ∈ s, f ≤ 𝓝 x

```

### cauchy_iff

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L47-L53

Excerpt SHA256: ec670cce44cc90cc9a0d2d516d49bd8f446fe316c14d6dae67921cbc3a4849ae

```lean
theorem cauchy_iff' {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ s ∈ 𝓤 α, ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, (x, y) ∈ s :=
  (𝓤 α).basis_sets.cauchy_iff

theorem cauchy_iff {f : Filter α} : Cauchy f ↔ NeBot f ∧ ∀ s ∈ 𝓤 α, ∃ t ∈ f, t ×ˢ t ⊆ s :=
  cauchy_iff'.trans <| by
    simp only [subset_def, Prod.forall, mem_prod_eq, and_imp, forall_mem_comm]

```

### CauchySeq

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L184-L188

Excerpt SHA256: 69be93c7d9f789486fca70d690bc417ed6bfc046421efd74ce8cf23535036dc7

```lean
/-- Cauchy sequences. Usually defined on ℕ, but often it is also useful to say that a function
defined on ℝ is Cauchy at +∞ to deduce convergence. Therefore, we define it in a type class that
is general enough to cover both ℕ and ℝ, which are the main motivating examples. -/
def CauchySeq [Preorder β] (u : β → α) :=
  Cauchy (atTop.map u)

```

### CompleteSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Cauchy.lean#L368-L373

Excerpt SHA256: 11cb273661eccc126e169d1905a8f37fd8f8d051d7118fa067f22b116b366c75

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

Excerpt SHA256: 7dd91310d3eccf779c254b58ca90f4f73cf856307fd3ad0894021c9ef38077e1

```lean
/-- If `univ` is complete, the space is a complete space -/
theorem completeSpace_of_isComplete_univ (h : IsComplete (univ : Set α)) : CompleteSpace α :=
  ⟨fun hf => let ⟨x, _, hx⟩ := h _ hf ((@principal_univ α).symm ▸ le_top); ⟨x, hx⟩⟩

theorem completeSpace_iff_isComplete_univ : CompleteSpace α ↔ IsComplete (univ : Set α) :=
  ⟨@isComplete_univ α _, completeSpace_of_isComplete_univ⟩

```

## Pinned source: Mathlib/Topology/Defs/Filter.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean

SHA256: 3b2ffc8154a531b4f0d3b36aa75ee08635c0df31884ba83baf1b0b0283c13748

Git blob SHA1: 343fd3e5f576a8e0f0f040eb2df8e5c309106655

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/

```

### nhds

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L127-L134

Excerpt SHA256: 50aa67ca57c8473255d83882eea110cc29269ae9a77d58cae57886b24f0bfa07

```lean
/-- A set is called a neighborhood of `x` if it contains an open set around `x`. The set of all
neighborhoods of `x` forms a filter, the neighborhood filter at `x`, is here defined as the
infimum over the principal filters of all open sets containing `x`. -/
irreducible_def nhds (x : X) : Filter X :=
  ⨅ s ∈ { s : Set X | x ∈ s ∧ IsOpen s }, 𝓟 s

@[inherit_doc]
scoped[Topology] notation "𝓝" => nhds

```

## Pinned source: Mathlib/Topology/Neighborhoods.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Neighborhoods.lean

SHA256: ef0e4d65986641366ffcc380a613f210207fee31e8640e1488a8cae41395383a

Git blob SHA1: 8bfc6cc6c85396ab77a34b0725508d165b3903f4

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/

```

### mem_nhds_iff

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Neighborhoods.lean#L64-L66

Excerpt SHA256: 3920d4125f26e7f74ea0eb050f41fa4c4f00ef056b57524cd6b93066efb1d515

```lean
theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t :=
  (nhds_basis_opens x).mem_iff.trans <| exists_congr fun _ =>
    ⟨fun h => ⟨h.2, h.1.2, h.1.1⟩, fun h => ⟨⟨h.2.2, h.2.1⟩, h.1⟩⟩

```

## Pinned source: Mathlib/Order/Filter/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean

SHA256: d0b1e4022a3910b2768e8786a3a66d701db0cb4c59c055b3bd17ec4cd28a60e5

Git blob SHA1: 760285d16af8795fa73313254a28aa651c9d0883

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/

```

### Filter

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L71-L83

Excerpt SHA256: 0d537bbb0e92a3e5a1c9a1c33b713a8c1351c8f23d9b835133dba47b1c526200

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

Excerpt SHA256: a99ab18fd794b2e2b76c56bfa8532bcb16e403417f304a87285b776cb5782aca

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

Excerpt SHA256: 9ef3719fef82cd6404287f98980c3054bbce035b372a7bd938e80fccdc056a78

```lean
/-- Product of filters. This is the filter generated by Cartesian products
of elements of the component filters. -/
instance instSProd : SProd (Filter α) (Filter β) (Filter (α × β)) where
  sprod f g := f.comap Prod.fst ⊓ g.comap Prod.snd

theorem prod_eq_inf (f : Filter α) (g : Filter β) : f ×ˢ g = f.comap Prod.fst ⊓ g.comap Prod.snd :=
  rfl

/-- The product of an indexed family of filters. -/

```

### Filter.principal

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L147-L158

Excerpt SHA256: b9ac7078f265922dbe9c103f5320642c8b0341f855d674b959a051d39edcee33

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

### Filter.NeBot

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L268-L277

Excerpt SHA256: 1488e11444dcb443471e0955a43cd486caed1add58d2970214794e265e2b9627

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

### Filter.map-Tendsto

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L405-L423

Excerpt SHA256: e6f89a53ff1df261c7705955e27a8d227354e5926f369e20b02c35ad98be4313

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

Excerpt SHA256: 362366ce36802bc59b3b10b58727f2c6636d06fcf2d31241e21f8d26a375d782

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

## Pinned source: Mathlib/Order/Filter/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Basic.lean

SHA256: 5dac9f84ef61915588e250fbb6e816ecf3d3183a94aa7e31f85e390baeb30afb

Git blob SHA1: 13734fc09a2dff6db46ca52140aceb45d45eccd8

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/

```

### Filter.le_principal_iff

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Basic.lean#L365-L367

Excerpt SHA256: d08e61a69841f2db9a4d86aa848cc71575f01b48205811c4cb5515695f163896

```lean
@[simp]
theorem le_principal_iff {s : Set α} {f : Filter α} : f ≤ 𝓟 s ↔ s ∈ f :=
  ⟨fun h => h Subset.rfl, fun hs _ ht => mem_of_superset hs ht⟩

```

## Pinned source: Mathlib/Order/Filter/Prod.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Prod.lean

SHA256: 2aa26b2b6beb3860fe1584961fe9f87d22c4d9cf7e719c6817a97c90dc244367

Git blob SHA1: 9ba0b26e290fe850ba43a785d59881ff873a8936

```lean
/-
Copyright (c) 2022 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Yury Kudryashov, Kevin H. Wilson, Heather Macbeth
-/

```

### Filter.mem_prod_iff

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Prod.lean#L52-L59

Excerpt SHA256: 55010dac263ead057dd2f09e496453866685af85abe7b22563b86eeeef24656c

```lean
theorem mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : Filter β} :
    s ∈ f ×ˢ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ ×ˢ t₂ ⊆ s := by
  constructor
  · rintro ⟨t₁, ⟨s₁, hs₁, hts₁⟩, t₂, ⟨s₂, hs₂, hts₂⟩, rfl⟩
    exact ⟨s₁, hs₁, s₂, hs₂, fun p ⟨h, h'⟩ => ⟨hts₁ h, hts₂ h'⟩⟩
  · rintro ⟨t₁, ht₁, t₂, ht₂, h⟩
    exact mem_inf_of_inter (preimage_mem_comap ht₁) (preimage_mem_comap ht₂) h


```

## Pinned source: Mathlib/Basic/ENNReal/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/ENNReal/Basic.lean

SHA256: 211629947deb3d78a8541202d33a9fed3d4c8f22215daea3d7d37209a824d947

Git blob SHA1: 75cadd3fae3f45e1e88abe228266fa115ef5552b

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/

```

### ENNReal.ofReal

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/ENNReal/Basic.lean#L230-L231

Excerpt SHA256: a3ab5f27deb3d03412fb6f307e41d5dbeea1c5c1fe971e76ebdebeafc0b20403

```lean
/-- `ofReal x` returns `x` if it is nonnegative, `0` otherwise. -/
protected def ofReal (r : Real) : ℝ≥0∞ := r.toNNReal

```

## Pinned source: Mathlib/Order/Filter/Tendsto.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Tendsto.lean

SHA256: 76800f92ca0414bd4f31e94719ac9cac2985bd2b083035380c3e32111e0405ce

Git blob SHA1: 7f85e578caf6eb1d37a45af5203cd059335be9b8

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/

```

### Filter.tendsto_def

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Tendsto.lean#L31-L33

Excerpt SHA256: 4c72dad4fe0238b5b998a3fbccd5b7f7095b1f6ff3b2d1495b3ab7566d8f0d00

```lean
theorem tendsto_def {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ :=
  Iff.rfl

```

## Pinned source: Mathlib/Order/Filter/AtTopBot/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/AtTopBot/Defs.lean

SHA256: 4091e8e0921cd9c2d70511ea017f5d9bdf861a9bc3e4408eb8625c81c1f6b621

Git blob SHA1: 6cf35ed92a409e5acf84c90305ecc7d1dd638619

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/

```

### Filter.atTop

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/AtTopBot/Defs.lean#L29-L40

Excerpt SHA256: 0414b8d5164f9dab4515dade24e8985b274e6226b91ba6e843fbbdd78d40d59b

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

## Pinned source: Mathlib/Topology/Bornology/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bornology/Basic.lean

SHA256: 427d7eff3bd67d3b8a3ba2df3636786b248405f789871161145d274f929d466e

Git blob SHA1: 4b142e1d604446eafb9ee39b6a39a492d687c997

```lean
/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

```

### Bornology

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bornology/Basic.lean#L48-L55

Excerpt SHA256: 6b90100aad31395953206030fe496a5a526e9db1473af7893d4213fc9d139bd8

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

## Pinned source: Mathlib/Topology/MetricSpace/Bounded.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Bounded.lean

SHA256: dbdb5dce531767c8e6b56f004d9d3a4cde9173a5a11ef40733a86cb432cadd2b

Git blob SHA1: b47b2b389eebc08df32ef3a6f450f350c389cfcd

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/

```

### Metric.diam

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Bounded.lean#L405-L411

Excerpt SHA256: 6619834688c217d42f16d3c8e78f41e3c88e5181286323b6d8d39411c9d13864

```lean
/-- The diameter of a set in a metric space. To get controllable behavior even when the diameter
should be infinite, we express it in terms of the `ediam` -/
noncomputable def diam (s : Set α) : ℝ :=
  ENNReal.toReal (ediam s)

/-- The diameter of a set is always nonnegative -/
theorem diam_nonneg : 0 ≤ diam s :=

```

### Metric.nonempty_iInter_of_nonempty_biInter

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Bounded.lean#L564-L570

Excerpt SHA256: 17aa72fea3bce982cdc3613292981d760ee2ed9bbb705423938181d1d451ec18

```lean
/-- In a complete space, if a family of closed sets with diameter tending to `0` is such that each
finite intersection is nonempty, then the total intersection is also nonempty. -/
theorem nonempty_iInter_of_nonempty_biInter [CompleteSpace α] {s : ℕ → Set α}
    (hs : ∀ n, IsClosed (s n)) (h's : ∀ n, IsBounded (s n)) (h : ∀ N, (⋂ n ≤ N, s n).Nonempty)
    (h' : Tendsto (fun n => diam (s n)) atTop (𝓝 0)) : (⋂ n, s n).Nonempty :=
  (hs 0).isComplete.nonempty_iInter_of_nonempty_biInter hs h's h h'


```

## Pinned source: Mathlib/Topology/EMetricSpace/Diam.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/EMetricSpace/Diam.lean

SHA256: 699ba791a149bdcdc24e9d7d650aa34925e04947d38df7e7c1ef9c9bd195822f

Git blob SHA1: d5a39e2f435e837f92a9ed3c804f61d9f6240bbf

```lean
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/

```

### Metric.ediam

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/EMetricSpace/Diam.lean#L24-L34

Excerpt SHA256: fa87de7eab6b342af268a7e064d1b0518a89b8b9b4f35dc85569dfcd943503bb

```lean

namespace Metric

section WeakPseudoEMetricSpace

/-- The diameter of a set in a pseudoemetric space as an extended nonnegative real number. -/
noncomputable def ediam [EDist X] (s : Set X) :=
  ⨆ (x ∈ s) (y ∈ s), edist x y

variable [TopologicalSpace X] [WeakPseudoEMetricSpace X]


```

## Pinned source: Mathlib/Basic/Countable/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Countable/Defs.lean

SHA256: d42047c8b18f28b7eba8ceca5867e472fcb8e840ac3499f88d3cd1d01451bb9f

Git blob SHA1: 2718dae9396dc0acff5f8b703d3587512b0281db

```lean
/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

```

### Countable

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Countable/Defs.lean#L41-L46

Excerpt SHA256: 551b5558571ec8d95682ed77589bddacda46501f10be4eef3efb6971e2a241e9

```lean
class Countable (α : Sort u) : Prop where
  /-- A type `α` is countable if there exists an injective map `α → ℕ`. -/
  exists_injective_nat' : ∃ f : α → ℕ, Injective f

lemma Countable.exists_injective_nat (α : Sort u) [Countable α] : ∃ f : α → ℕ, Injective f :=
  Countable.exists_injective_nat'

```

## Pinned source: Mathlib/Data/Set/Countable.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Countable.lean

SHA256: 047d0f370cc830214b8dba702ec49434af0072523561404e40a314d2a5f24b98

Git blob SHA1: f5ffd2035308f61e38f10aad4df99b2405ec519a

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

```

### Set.Countable

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Countable.lean#L40-L49

Excerpt SHA256: 029b5880e2f8d6ee503311ecdcfba5d91268eceeb5194b1788413175bcb3ccd5

```lean
namespace Set

/-- A set `s` is countable if the corresponding subtype is countable,
i.e., there exists an injective map `f : s → ℕ`.

Note that this is an abbreviation, so `hs : Set.Countable s` in the proof context
is the same as an instance `Countable s`.
For a constructive version, see `Encodable`.
-/
protected def Countable (s : Set α) : Prop := Countable s

```

### nonempty-countable-enumeration

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Countable.lean#L128-L135

Excerpt SHA256: 9f910f7c565b48c923524f064214b8df96db7ea66273207d6a64f00608489b1a

```lean
/-- A non-empty set is countable iff there exists a surjection from the
natural numbers onto the subtype induced by the set.
-/
protected theorem countable_iff_exists_surjective {s : Set α} (hs : s.Nonempty) :
    s.Countable ↔ ∃ f : ℕ → s, Surjective f :=
  @countable_iff_exists_surjective s hs.to_subtype

alias ⟨Countable.exists_surjective, _⟩ := Set.countable_iff_exists_surjective

```

## Pinned source: Mathlib/Topology/Metrizable/CompletelyMetrizable.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/CompletelyMetrizable.lean

SHA256: 45e2fe2d79f14e9cf4e87f13f413eef94b418384fc3eaad3dce7b1a730ed54c9

Git blob SHA1: a09f9b3b228345d4c4648901cbaa79885a10349f

```lean
/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/

```

### IsCompletelyMetrizableSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/CompletelyMetrizable.lean#L154-L156

Excerpt SHA256: b3d0593275db87c4c9e59e149d56341f6f3e4ec372a4e857cd945bd4adc1fe34

```lean
class IsCompletelyMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  complete : ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧
    @CompleteSpace X m.toUniformSpace

```

### compatible-complete-metric

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/CompletelyMetrizable.lean#L191-L211

Excerpt SHA256: 20644352ac64e08eda5aff19295568ff9379aa8a2327cc5b165d1e4d36c4f61e

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

## Pinned source: Mathlib/Topology/MetricSpace/Polish.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Polish.lean

SHA256: 71c9682ea53f194d1587fbd41695e35cc7fb8f51b1503f695ba4adfb15c52059

Git blob SHA1: ec205e848d4f8eabd112e1eb2c68327c0fac206a

```lean
/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

```

### PolishSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Polish.lean#L62-L63

Excerpt SHA256: 608a012181e874c09850107d4076cabf5aff90c8375361ce78c88b3c1ecc0210

```lean
class PolishSpace (α : Type*) [h : TopologicalSpace α] : Prop
    extends SecondCountableTopology α, IsCompletelyMetrizableSpace α

```

## Pinned source: Mathlib/Topology/Defs/Induced.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean

SHA256: ba804ff6a2bd28aea83da56dfc339e565745a088d7aeac977643410f1dae8f74

Git blob SHA1: 7526293e644df38a5a2564f8c52a2bd7f561fc82

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/

```

### induced

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean#L64-L67

Excerpt SHA256: 878b69c8488a10bac25ce164587ebbe29156ddb4fddd3fe1e9a3911d8bdd8110

```lean
def induced (f : X → Y) (t : TopologicalSpace Y) : TopologicalSpace X where
  IsOpen s := ∃ t, IsOpen t ∧ f ⁻¹' t = s
  isOpen_univ := ⟨univ, isOpen_univ, preimage_univ⟩
  isOpen_inter := by

```

## Pinned source: Mathlib/Topology/Bases.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean

SHA256: fbd29cb53487d8ff54efda38cd831d4966a19a052654ef39a09352753986d1d6

Git blob SHA1: 4165527ffdf10c235881bc6738e99ad2bf6b1b07

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/

```

### SecondCountableTopology

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean#L793-L795

Excerpt SHA256: be0e6df4a04de8ef9819f4c545edf341efed762b08226cf4af131b90d05813b4

```lean
class _root_.SecondCountableTopology : Prop where
  /-- There exists a countable set of sets that generates the topology. -/
  is_open_generated_countable : ∃ b : Set (Set α), b.Countable ∧ t = TopologicalSpace.generateFrom b

```

### IsTopologicalBasis

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean#L73-L79

Excerpt SHA256: 06ef0a524e711562ab10d1c840fe57620c7dd2df3111034ac2d8f81c0424ed42

```lean
structure IsTopologicalBasis (s : Set (Set α)) : Prop where
  /-- For every point `x`, the set of `t ∈ s` such that `x ∈ t` is directed downwards. -/
  exists_subset_inter : ∀ t₁ ∈ s, ∀ t₂ ∈ s, ∀ x ∈ t₁ ∩ t₂, ∃ t₃ ∈ s, x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂
  /-- The sets from `s` cover the whole space. -/
  sUnion_eq : ⋃₀ s = univ
  /-- The topology is generated by sets from `s`. -/
  eq_generateFrom : t = generateFrom s

```

### basis-second-countable

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean#L797-L804

Excerpt SHA256: 1d2bbba6b36e34e85c48c0bfe5c5d05b8b445469e9ff2228dad8646ac50518b3

```lean
protected theorem IsTopologicalBasis.secondCountableTopology {b : Set (Set α)}
    (hb : IsTopologicalBasis b) (hc : b.Countable) : SecondCountableTopology α :=
  ⟨⟨b, hc, hb.eq_generateFrom⟩⟩

lemma SecondCountableTopology.mk' {α} {b : Set (Set α)} (hc : b.Countable) :
    @SecondCountableTopology α (generateFrom b) :=
  @SecondCountableTopology.mk α (generateFrom b) ⟨b, hc, rfl⟩


```

### exists_countable_basis

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean#L811-L815

Excerpt SHA256: 23a21589d0b5dab34322c819ed07e5a123b4b506ffdd168a2eb01177dc1e1af5

```lean
theorem exists_countable_basis [SecondCountableTopology α] :
    ∃ b : Set (Set α), b.Countable ∧ ∅ ∉ b ∧ IsTopologicalBasis b := by
  obtain ⟨b, hb₁, hb₂⟩ := @SecondCountableTopology.is_open_generated_countable α _ _
  refine ⟨_, ?_, notMem_sdiff_of_mem ?_, (isTopologicalBasis_of_subbasis hb₂).sdiff_empty⟩
  exacts [((countable_ofPred_finite_subset hb₁).image _).mono sdiff_subset, rfl]

```

### open-union-countable

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean#L930-L941

Excerpt SHA256: 16328afa0beea669b91aaa80230b1d152898d3cf700e7213dc0a10ac60a211d1

```lean
/-- In a second-countable space, an open set, given as a union of open sets,
is equal to the union of countably many of those sets.
In particular, any open covering of `α` has a countable subcover: α is a Lindelöf space. -/
theorem isOpen_iUnion_countable [SecondCountableTopology α] {ι} (s : ι → Set α)
    (H : ∀ i, IsOpen (s i)) : ∃ T : Set ι, T.Countable ∧ ⋃ i ∈ T, s i = ⋃ i, s i := by
  let B := { b ∈ countableBasis α | ∃ i, b ⊆ s i }
  choose f hf using fun b : B => b.2.2
  have : Countable B := ((countable_countableBasis α).mono (sep_subset _ _)).to_subtype
  refine ⟨_, countable_range f, (iUnion₂_subset_iUnion _ _).antisymm (sUnion_subset ?_)⟩
  rintro _ ⟨i, rfl⟩ x xs
  rcases (isBasis_countableBasis α).exists_subset_of_mem_open xs (H _) with ⟨b, hb, xb, bs⟩
  exact ⟨_, ⟨_, rfl⟩, _, ⟨⟨⟨_, hb, _, bs⟩, rfl⟩, rfl⟩, hf _ xb⟩

```

## Pinned source: Mathlib/Topology/Order.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean

SHA256: 2705ffc65ea519f775d4e9678578a2dbb18f096325f857c6267ac2bd83af86c5

Git blob SHA1: b8acdd3aee23b43330bc36aa8f7f1819a16a2a55

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/

```

### generateFrom

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean#L62-L75

Excerpt SHA256: 157d25ad393ea6c2266bed17f78f91f1658d33d3609091b788dfa8c70f0692a4

```lean
inductive GenerateOpen (g : Set (Set α)) : Set α → Prop
  | basic : ∀ s ∈ g, GenerateOpen g s
  | univ : GenerateOpen g univ
  | inter : ∀ s t, GenerateOpen g s → GenerateOpen g t → GenerateOpen g (s ∩ t)
  | sUnion : ∀ S : Set (Set α), (∀ s ∈ S, GenerateOpen g s) → GenerateOpen g (⋃₀ S)

/-- The smallest topological space containing the collection `g` of basic sets -/
@[instance_reducible]
def generateFrom (g : Set (Set α)) : TopologicalSpace α where
  IsOpen := GenerateOpen g
  isOpen_univ := GenerateOpen.univ
  isOpen_inter := GenerateOpen.inter
  isOpen_sUnion := GenerateOpen.sUnion


```

### DiscreteTopology

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean#L307-L311

Excerpt SHA256: 26015841fe28c8608aba85513b1657bd58475e98010121e1391aeb8726391b3f

```lean
/-- A topological space is discrete if every set is open, that is,
  its topology equals the discrete topology `⊥`. -/
class DiscreteTopology (α : Type*) [t : TopologicalSpace α] : Prop where
  /-- The `TopologicalSpace` structure on a type with discrete topology is equal to `⊥`. -/
  eq_bot : t = ⊥

```

### Nat.discrete-topology

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean#L578-L579

Excerpt SHA256: f2810160c15385f3aa530a9d5d6ccd928f619409d9a38548f2ae5056f5ccc9ae

```lean
instance : TopologicalSpace ℕ := ⊥
instance : DiscreteTopology ℕ := ⟨rfl⟩

```

## Pinned source: Mathlib/Topology/Constructions.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions.lean

SHA256: 47de73fc60746ec4c31fa6e3fcb6d7fe8fbbcf5dbc88c0471fc017040a26467f

Git blob SHA1: 91a7136cc7b39e609f8becbf9e0785069bb2610d

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/

```

### Pi.product-topology

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions.lean#L66-L68

Excerpt SHA256: 8d6d3bc58b2c45da4e5c3bc1a5c7df8aa12981d05fd20ae4735702d0dcaf5c76

```lean
instance Pi.topologicalSpace {ι : Type*} {Y : ι → Type v} [t₂ : (i : ι) → TopologicalSpace (Y i)] :
    TopologicalSpace ((i : ι) → Y i) :=
  ⨅ i, induced (fun f => f i) (t₂ i)

```

## Pinned source: Mathlib/Data/Set/Operations.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean

SHA256: 60e5fa9adbd7d068a553d5a28875f5250e0a20771b5179f9f552882d0865c68e

Git blob SHA1: f5d18fca655f6bf3079f859060f3738b5f2bc089

```lean
/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Johannes Hölzl, Reid Barton, Kim Morrison, Patrick Massot, Kyle Miller,
Minchao Wu, Yury Kudryashov, Floris van Doorn
-/

```

### Set.range

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean#L173-L173

Excerpt SHA256: 6ea5f38bede17452fab4c6025aa7489ccb2b191c13d4a1ce86fc1d2bc8a6bbd0

```lean
def range (f : ι → α) : Set α := {x | ∃ y, f y = x}

```

### open-image-Set.preimage

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean#L135-L135

Excerpt SHA256: bdbb3311188d718892907fb87ac66f86bfb45fc4cbcefeb9b80864b388966258

```lean
def preimage (f : α → β) (s : Set β) : Set α := {x | f x ∈ s}

```

## Pinned source: Mathlib/Topology/MetricSpace/PiNat.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/PiNat.lean

SHA256: a6d5b738f8217038bc1b2889f5fa0f0ea84b544dbc21761e90b35dcf8cd0d669

Git blob SHA1: 9037e11c4d4eeb6bcd61b008be2f6f95426d2181

```lean
/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

```

### PiNat.cylinder

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/PiNat.lean#L109-L110

Excerpt SHA256: a45172b1a533ce6d7736a8b2d4709829b0a6c4ed21959e84070312d88432e511

```lean
def cylinder (x : ∀ n, E n) (n : ℕ) : Set (∀ n, E n) :=
  { y | ∀ i, i < n → y i = x i }

```

### PiNat.res

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/PiNat.lean#L191-L193

Excerpt SHA256: b7c50e4330d7be3ef49d1dbffb21714607d69decef6090de175e38a4106a39ae

```lean
def res (x : ℕ → α) : ℕ → List α
  | 0 => nil
  | Nat.succ n => x n :: res x n

```

### PiNat.res-equivalence

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/PiNat.lean#L195-L239

Excerpt SHA256: 8ba98ec91cfb75501b47e742278333ac8844f08fe5e4c32aa10f2f905d1cb6bc

```lean
@[simp]
theorem res_zero (x : ℕ → α) : res x 0 = @nil α :=
  rfl

@[simp]
theorem res_succ (x : ℕ → α) (n : ℕ) : res x n.succ = x n :: res x n :=
  rfl

@[simp]
theorem res_length (x : ℕ → α) (n : ℕ) : (res x n).length = n := by induction n <;> simp [*]

/-- The restrictions of `x` and `y` to `n` are equal if and only if `x m = y m` for all `m < n`. -/
theorem res_eq_res {x y : ℕ → α} {n : ℕ} :
    res x n = res y n ↔ ∀ ⦃m⦄, m < n → x m = y m := by
  constructor <;> intro h
  · induction n with
    | zero => simp
    | succ n ih =>
      intro m hm
      rw [Nat.lt_succ_iff_lt_or_eq] at hm
      simp only [res_succ, cons.injEq] at h
      rcases hm with hm | hm
      · exact ih h.2 hm
      rw [hm]
      exact h.1
  · induction n with
    | zero => simp
    | succ n ih =>
      simp only [res_succ, cons.injEq]
      refine ⟨h (Nat.lt_succ_self _), ih fun m hm => ?_⟩
      exact h (hm.trans (Nat.lt_succ_self _))

theorem res_injective : Injective (@res α) := by
  intro x y h
  ext n
  apply res_eq_res.mp _ (Nat.lt_succ_self _)
  rw [h]

/-- `cylinder x n` is equal to the set of sequences `y` with the same restriction to `n` as `x`. -/
theorem cylinder_eq_res (x : ℕ → α) (n : ℕ) :
    cylinder x n = { y | res y n = res x n } := by
  ext y
  dsimp [cylinder]
  rw [res_eq_res]


```

### PiNat.cylinder-basis

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/PiNat.lean#L344-L368

Excerpt SHA256: 808b0ee14e623257bb1b10fd817064f716381635545a0bc70872163046b929c0

```lean
theorem isOpen_cylinder (x : ∀ n, E n) (n : ℕ) : IsOpen (cylinder x n) := by
  rw [PiNat.cylinder_eq_pi]
  exact isOpen_set_pi (Finset.range n).finite_toSet fun a _ => isOpen_discrete _

theorem isTopologicalBasis_cylinders :
    IsTopologicalBasis { s : Set (∀ n, E n) | ∃ (x : ∀ n, E n) (n : ℕ), s = cylinder x n } := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro u ⟨x, n, rfl⟩
    apply isOpen_cylinder
  · intro x u hx u_open
    obtain ⟨v, ⟨U, F, -, rfl⟩, xU, Uu⟩ :
        ∃ v ∈ { S : Set (∀ i : ℕ, E i) | ∃ (U : ∀ i : ℕ, Set (E i)) (F : Finset ℕ),
          (∀ i : ℕ, i ∈ F → U i ∈ { s : Set (E i) | IsOpen s }) ∧ S = (F : Set ℕ).pi U },
        x ∈ v ∧ v ⊆ u :=
      (isTopologicalBasis_pi fun n : ℕ => isTopologicalBasis_opens).exists_subset_of_mem_open hx
        u_open
    rcases Finset.bddAbove F with ⟨n, hn⟩
    refine ⟨cylinder x (n + 1), ⟨x, n + 1, rfl⟩, self_mem_cylinder _ _, Subset.trans ?_ Uu⟩
    intro y hy
    suffices ∀ i : ℕ, i ∈ F → y i ∈ U i by simpa
    intro i hi
    have : y i = x i := mem_cylinder_iff.1 hy i ((hn hi).trans_lt (lt_add_one n))
    rw [this]
    simp only [Set.mem_pi, Finset.mem_coe] at xU
    exact xU i hi

```

## Pinned source: Mathlib/Topology/MetricSpace/CantorScheme.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/CantorScheme.lean

SHA256: 49e509d69864b088f042d73153f4c33bdc3521a2f513306d55924a326d134246

Git blob SHA1: 729512ff8b52bb27c9e6e2590387a9c86ff27b29

```lean
/-
Copyright (c) 2023 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/

```

### CantorScheme.inducedMap

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/CantorScheme.lean#L57-L58

Excerpt SHA256: 70f61defa0e4c8e49d277b27d0000f31f7ed216b4777c0c85c821accfe6fc8e8

```lean
noncomputable def inducedMap : Σ s : Set (ℕ → β), s → α :=
  ⟨{x | Set.Nonempty (⋂ n : ℕ, A (res x n))}, fun x => x.property.some⟩

```

### CantorScheme.ClosureAntitone

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/CantorScheme.lean#L68-L69

Excerpt SHA256: 9a8bb3b136a517a67f75bc39a340666473feab8e0d4c120a864a94e94150b74a

```lean
def ClosureAntitone [TopologicalSpace α] : Prop :=
  ∀ l : List β, ∀ a : β, closure (A (a :: l)) ⊆ A l

```

### CantorScheme.VanishingDiam

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/CantorScheme.lean#L119-L120

Excerpt SHA256: 2ae7ceeb838f9075f3ccae49045d4854c137f0f5219179910c289891991b4563

```lean
def VanishingDiam : Prop :=
  ∀ x : ℕ → β, Tendsto (fun n : ℕ => Metric.ediam (A (res x n))) atTop (𝓝 0)

```

### CantorScheme.map_mem

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/CantorScheme.lean#L77-L82

Excerpt SHA256: 89498421831c64e2f5ea797ee3fbff591f14e370911af4503773641c88c5509b

```lean
/-- If `x` is in the domain of the induced map of a scheme `A`,
its image under this map is in each set along the corresponding branch. -/
theorem map_mem (x : (inducedMap A).1) (n : ℕ) : (inducedMap A).2 x ∈ A (res x n) := by
  have := x.property.some_mem
  rw [mem_iInter] at this
  exact this n

```

### CantorScheme.continuity

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/CantorScheme.lean#L137-L156

Excerpt SHA256: f55e983ebee6aa6a736b3045df8d14b7d02c952d00f3de677efe321ac9d30fac

```lean

/-- A scheme with vanishing diameter along each branch induces a continuous map. -/
theorem VanishingDiam.map_continuous [TopologicalSpace β] [DiscreteTopology β]
    (hA : VanishingDiam A) : Continuous (inducedMap A).2 := by
  rw [Metric.continuous_iff']
  rintro x ε ε_pos
  obtain ⟨n, hn⟩ := hA.dist_lt _ ε_pos x
  rw [_root_.eventually_nhds_iff]
  refine ⟨(↑)⁻¹' cylinder x.1 n, ?_, ?_, by simp⟩
  · rintro y hyx
    rw [mem_preimage, Subtype.coe_mk, cylinder_eq_res, mem_ofPred] at hyx
    apply hn
    · rw [← hyx]
      apply map_mem
    apply map_mem
  apply continuous_subtype_val.isOpen_preimage
  apply isOpen_cylinder

/-- A scheme on a complete space with vanishing diameter
such that each set contains the closure of its children

```

### CantorScheme.totality

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/CantorScheme.lean#L158-L184

Excerpt SHA256: 6e565df24accca950edb176f7480557c49686a10b2c152c53a9aecdfdde88e7e

```lean
theorem ClosureAntitone.map_of_vanishingDiam [CompleteSpace α] (hdiam : VanishingDiam A)
    (hanti : ClosureAntitone A) (hnonempty : ∀ l, (A l).Nonempty) : (inducedMap A).1 = univ := by
  rw [eq_univ_iff_forall]
  intro x
  choose u hu using fun n => hnonempty (res x n)
  have umem : ∀ n m : ℕ, n ≤ m → u m ∈ A (res x n) := by
    have : Antitone fun n : ℕ => A (res x n) := by
      refine antitone_nat_of_succ_le ?_
      intro n
      apply hanti.antitone
    intro n m hnm
    exact this hnm (hu _)
  have : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε ε_pos
    obtain ⟨n, hn⟩ := hdiam.dist_lt _ ε_pos x
    use n
    intro m₀ hm₀ m₁ hm₁
    apply hn <;> apply umem <;> assumption
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete this
  use y
  rw [mem_iInter]
  intro n
  apply hanti _ (x n)
  apply mem_closure_of_tendsto hy
  rw [eventually_atTop]
  exact ⟨n.succ, umem _⟩

```

## Pinned source: Mathlib/Basic/NNReal/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/NNReal/Defs.lean

SHA256: 5a94f78b3f6ce87106eea63ea8bfa48647de38cf2e51bff75f06a311ef821c99

Git blob SHA1: 17a16cab929f5ab10979e46078284068c567bf88

```lean
/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

```

### Real.toNNReal

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/NNReal/Defs.lean#L154-L156

Excerpt SHA256: 6202c76ac8dc217a4fa61594555ea69c65c321fd190b07503ee4ea612120a105

```lean
/-- Reinterpret a real number `r` as a non-negative real number. Returns `0` if `r < 0`. -/
def _root_.Real.toNNReal (r : ℝ) : ℝ≥0 :=
  .mk (max r 0) (le_max_right _ _)

```

## Core definition: Function.Surjective

For every target b there exists source a with f a=b; no injectivity or nonemptiness is hidden.

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/lean/Init/Data/Function.lean#L59-L63

Full-file SHA256: 88217ed8ec91da1ec655c8a10f737b659a4570b4c05dbd6b084162a3157cf030

Excerpt SHA256: 81f3c1294b8b4f215a4b094823922dbd95234cd6a53280e94f6fd6d7280c0148

```lean
/-- A function `f : α → β` is called surjective if every `b : β` is equal to `f a`
for some `a : α`. -/
@[expose]
def Surjective (f : α → β) : Prop :=
  ∀ b, Exists fun a => f a = b

```

## Core definition: Nonempty

A proposition with constructor carrying an element of the sort. The empty codomain is excluded explicitly; the source natural-number function space is inhabited.

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/lean/Init/Prelude.lean#L839-L841

Full-file SHA256: cc9f337a5d8bd00768121701bceb0661ac63e01831a9aa34b282f37c689a6c39

Excerpt SHA256: 409b9d791b14a599f13bb14741bdfbfc112bc04bd4fc41d9924083fa47df7598

```lean
class inductive Nonempty (α : Sort u) : Prop where
  /-- If `val : α`, then `α` is nonempty. -/
  | intro (val : α) : Nonempty α

```
