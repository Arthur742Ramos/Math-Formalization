# Material imported definitions

Exact Mathlib pin `065356127b1dc0016f66b7283ce0ce2c4055aa55`; Lean `4.35.0-rc2`.

This is an authored source/semantic inventory. Separate Challenge/Solution bridge modules are prepared; this author has not compiled them. Exact hashes authenticate retained bytes, not semantic fidelity, inventory completeness or editorial acceptance. Shared upstream excerpts are adapted from the earlier Baire inventory at the same pin; mathematical descriptions below refer only to this binary topological proof.

## TopologicalSpace

Open sets closed under the whole space, finite intersections and arbitrary unions. All statements use the supplied topology. Metrizability concerns this same topology; the construction itself is topological.

Used by: CantorCharacterization.exists_clopen_split, CantorCharacterization.exists_deciding_split, CantorCharacterization.exists_binary_scheme, CantorCharacterization.BinaryScheme.continuous_code, CantorCharacterization.BinaryScheme.surjective_code, CantorCharacterization.BinaryScheme.injective_code, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.cantor_hasClopenBasis, CantorCharacterization.cantor_perfectSpace, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## IsOpen

The open-set predicate of the supplied topology. All binary cells are clopen. Local constancy of each address coordinate on an open cell proves continuity.

Used by: CantorCharacterization.exists_clopen_split, CantorCharacterization.exists_deciding_split, CantorCharacterization.exists_binary_scheme, CantorCharacterization.BinaryScheme.continuous_code, CantorCharacterization.BinaryScheme.surjective_code, CantorCharacterization.BinaryScheme.injective_code, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.cantor_hasClopenBasis, CantorCharacterization.cantor_perfectSpace, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## IsClosed

A set whose complement is open. Every scheme cell is closed. Nested nonempty closed cells in the compact whole space have a nonempty intersection; no metric completeness argument is used.

Used by: CantorCharacterization.exists_clopen_split, CantorCharacterization.exists_deciding_split, CantorCharacterization.exists_binary_scheme, CantorCharacterization.BinaryScheme.continuous_code, CantorCharacterization.BinaryScheme.surjective_code, CantorCharacterization.BinaryScheme.injective_code, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.cantor_hasClopenBasis, CantorCharacterization.cantor_perfectSpace, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## Set.Nonempty

There exists a point belonging to the set. Every binary cell is nonempty, including both children at every split. The full iff separately excludes the empty space.

Used by: CantorCharacterization.exists_clopen_split, CantorCharacterization.exists_deciding_split, CantorCharacterization.exists_binary_scheme, CantorCharacterization.BinaryScheme.continuous_code, CantorCharacterization.BinaryScheme.surjective_code, CantorCharacterization.BinaryScheme.injective_code, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.cantor_hasClopenBasis, CantorCharacterization.cantor_perfectSpace, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## IsClopen

The conjunction of closedness and openness. Cells and enumerated basis members are genuinely clopen; no replacement by compactness or total disconnectedness is made.

Used by: CantorCharacterization.exists_clopen_split, CantorCharacterization.exists_deciding_split, CantorCharacterization.exists_binary_scheme, CantorCharacterization.BinaryScheme.continuous_code, CantorCharacterization.BinaryScheme.surjective_code, CantorCharacterization.BinaryScheme.injective_code, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.cantor_hasClopenBasis, CantorCharacterization.cantor_perfectSpace, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## Countable

A type admits an injection into the naturals. Only the countable basis index subtype is enumerated. Repeated basis sets are permitted; each split still has two distinct nonempty children.

Used by: CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## Set.Countable

The subtype of elements of the set is countable. A countable subfamily of the clopen basis is selected; the underlying Cantor space is not asserted countable.

Used by: CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## SecondCountableTopology

The supplied topology is generated by a countable family of subsets. The explicit second-countable sufficiency enumerates a countable clopen basis. Compact metrizability supplies second countability in the standard sufficient direction.

Used by: CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## TopologicalSpace.IsTopologicalBasis

A family generating the topology, covering the space, and refining intersections at each point. The proved neighborhood/open-set characterizations justify clopen refinements and point separation. Basis decisions imply injectivity, while generic continuity and compact-branch realization do not assume this family is a basis.

Used by: CantorCharacterization.exists_clopen_split, CantorCharacterization.exists_deciding_split, CantorCharacterization.exists_binary_scheme, CantorCharacterization.BinaryScheme.injective_code, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.cantor_hasClopenBasis, CantorCharacterization.cantor_perfectSpace, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## Continuous

Preimages of open codomain sets are open. Each Bool address coordinate is locally constant on an open scheme cell; continuity into the product is coordinatewise. A continuous bijection from compact X to Hausdorff Cantor space has continuous inverse.

Used by: CantorCharacterization.BinaryScheme.continuous_code, CantorCharacterization.BinaryScheme.surjective_code, CantorCharacterization.BinaryScheme.injective_code, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## Homeomorph

A bijection continuous in both directions. Extends Equiv with forward and inverse continuity. The proof uses the compact-to-Hausdorff continuous-equivalence theorem; continuous injection into a Cantor subset would not establish this result.

Used by: CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## Equiv

Two functions satisfying left and right inverse laws. Equiv.ofBijective uses separately proved injection and surjection of the address map. Homeomorph adds both continuity obligations.

Used by: CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## Function.Bijective

Injectivity and surjectivity together. Every branch is realized by compactness, and basis decisions distinguish different points. Both are needed for the equivalence.

Used by: CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## Disjoint

For sets, empty intersection. Literal lattice lower-bound definition is connected by the proved set-intersection equivalence. Binary siblings never share a point.

Used by: CantorCharacterization.exists_clopen_split, CantorCharacterization.exists_deciding_split, CantorCharacterization.exists_binary_scheme, CantorCharacterization.BinaryScheme.continuous_code, CantorCharacterization.BinaryScheme.surjective_code, CantorCharacterization.BinaryScheme.injective_code, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## Pairwise

The relation holds for every two distinct indices. This is used in the literal Hausdorff class field; sibling disjointness is specifically the false/true pair.

Used by: CantorCharacterization.exists_clopen_split, CantorCharacterization.exists_deciding_split, CantorCharacterization.exists_binary_scheme, CantorCharacterization.BinaryScheme.injective_code, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## Set.image

Values attained by a function on a specified domain set. Clopen basis transfer takes image neighborhoods under a homeomorphism, then pulls selected clopen sets back; all membership witnesses are retained.

Used by: CantorCharacterization.nonempty_homeomorph_iff.

## Set.preimage

Points whose function values belong to a specified target set. Literal continuity and clopen pullback use preimages, not an unjustified commutation of images and intersections.

Used by: CantorCharacterization.BinaryScheme.continuous_code, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## Set.range

The set of all values attained by a function. The enumerated family B has a range that is a topological basis; this is a range of sets, not the image of the coding map.

Used by: CantorCharacterization.BinaryScheme.injective_code, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## TopologicalSpace.induced

The topology consisting of preimages of opens under the specified map. The topology on Bool sequences is the infimum of coordinate-induced topologies. A topological embedding includes equality with the induced topology.

Used by: CantorCharacterization.BinaryScheme.continuous_code, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.cantor_hasClopenBasis, CantorCharacterization.cantor_perfectSpace, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## PiNat.cylinder

All sequences agreeing with the given sequence at coordinates strictly below n. Here coordinates are Bool, so paths are genuinely binary. Every finite cylinder is clopen; every cylinder contains a distinct point obtained by toggling coordinate n.

Used by: CantorCharacterization.cantor_hasClopenBasis, CantorCharacterization.cantor_perfectSpace, CantorCharacterization.nonempty_homeomorph_iff.

## PiNat.res

The first n coordinates stored in reverse order as a list. res x (n+1)=x n::res x n. The scheme uses exactly this child convention, and res_code explicitly equates the recursive address prefix with this reverse prefix.

Used by: CantorCharacterization.BinaryScheme.continuous_code, CantorCharacterization.BinaryScheme.surjective_code, CantorCharacterization.BinaryScheme.injective_code, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## DiscreteTopology

The given topology is the bottom, discrete topology. Each Bool coordinate is discrete. The product on all binary sequences is not discrete; finite-coordinate cylinders form its basis.

Used by: CantorCharacterization.BinaryScheme.continuous_code, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.cantor_hasClopenBasis, CantorCharacterization.cantor_perfectSpace, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## CompactSpace

The whole space is compact, with no separation axiom built in. Compactness is independent of Hausdorffness and nonemptiness. Nested nonempty closed cells yield every binary branch. The inverse continuity theorem uses the separate Hausdorff property of the codomain.

Used by: CantorCharacterization.BinaryScheme.surjective_code, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## IsCompact

Every open cover of the set has a finite subcover. Its literal definition uses cluster points of nontrivial filters supported on the set. The open-cover formulation is a proved equivalence. Only compactness of closed scheme cells in a compact ambient space is needed.

Used by: CantorCharacterization.BinaryScheme.surjective_code, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## ClusterPt

Every filter set meets every neighborhood of the point. Literal nontrivial intersection of the neighborhood filter and supplied filter. This allows the point itself; AccPt removes it using punctured neighborhoods.

Used by: CantorCharacterization.BinaryScheme.surjective_code, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## PerfectSpace

Every point is non-isolated. Literal field says the universe is Preperfect; Preperfect quantifies accumulation at each point, including punctured neighborhoods. Empty types satisfy this vacuously, so Nonempty is separate. In open nonempty cells it supplies two distinct points.

Used by: CantorCharacterization.exists_clopen_split, CantorCharacterization.exists_deciding_split, CantorCharacterization.exists_binary_scheme, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.cantor_perfectSpace, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## Preperfect

Every point of a set is an accumulation point of that same set. No closedness or nonemptiness is included. Its neighborhood equivalence explicitly supplies another point of the set in every neighborhood, distinct from the given point.

Used by: CantorCharacterization.exists_clopen_split, CantorCharacterization.exists_deciding_split, CantorCharacterization.exists_binary_scheme, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.cantor_perfectSpace, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## AccPt

Nontrivial intersection of the punctured-neighborhood filter with the supplied filter. For a principal set filter, every neighborhood contains a point of that set different from x. This is distinct from ClusterPt, which does not remove x.

Used by: CantorCharacterization.exists_clopen_split, CantorCharacterization.exists_deciding_split, CantorCharacterization.exists_binary_scheme, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.cantor_perfectSpace, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## nhdsWithin

Intersection of the neighborhood filter with the principal filter of a set. Punctured neighborhoods mean nhdsWithin x {x}ᶜ. Thus distinctness in PerfectSpace is literal and is not merely nontriviality of an ordinary neighborhood filter.

Used by: CantorCharacterization.exists_clopen_split, CantorCharacterization.exists_deciding_split, CantorCharacterization.exists_binary_scheme, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.cantor_perfectSpace, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## Filter.NeBot

The filter differs from the bottom filter. A nontrivial filter contains no empty set. In AccPt this applies after puncturing; in IsCompact the tested filters are required nontrivial.

Used by: CantorCharacterization.exists_clopen_split, CantorCharacterization.exists_deciding_split, CantorCharacterization.exists_binary_scheme, CantorCharacterization.BinaryScheme.surjective_code, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.cantor_perfectSpace, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## T2Space

Every two distinct points have disjoint open neighborhoods. Required explicitly in the second-countable sufficient core and injective-code contract. In the metrizable sufficient form it is derived from MetrizableSpace, not silently assumed by CompactSpace.

Used by: CantorCharacterization.exists_clopen_split, CantorCharacterization.exists_deciding_split, CantorCharacterization.exists_binary_scheme, CantorCharacterization.BinaryScheme.injective_code, CantorCharacterization.nonempty_homeomorph_of_secondCountable, CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## TopologicalSpace.MetrizableSpace

Pseudometrizability together with the T0 separation axiom. Literal parents are PseudoMetrizableSpace and T0Space. The pinned compatible metric construction supplies the familiar metric interpretation. Compact metrizable spaces are second-countable; no complete metric or diameter-decay choice is used by this proof.

Used by: CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## TopologicalSpace.PseudoMetrizableSpace

Existence of a compatible countably generated uniformity. Literal field supplies a UniformSpace whose topology equals the supplied topology and whose uniformity filter is countably generated. Compatible pseudometric construction is a theorem-level construction, not the literal class body.

Used by: CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## T0Space

Inseparable points must be equal. Inseparable means equality of neighborhood filters. This separation parent distinguishes metric from pseudometric compatibility.

Used by: CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## Inseparable

The two neighborhood filters are equal. This literal equality is used to express the T0 parent of MetrizableSpace.

Used by: CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## Filter.IsCountablyGenerated

The filter is generated by a countable family of sets. The literal field quantifies a countable set s and equality f=Filter.generate s; finite intersections and supersets form the generated filter. This is a uniformity property, distinct from topology second countability.

Used by: CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## UniformSpace

A compatible topology and symmetric composable uniformity on pairs. Only used inside the literal metrizable class expansion. No completeness or Cauchy filter assumption is added to the topological binary-scheme proof.

Used by: CantorCharacterization.nonempty_homeomorph, CantorCharacterization.nonempty_homeomorph_iff.

## Topology.IsEmbedding

An injective map inducing exactly the source topology. Homeomorph.isEmbedding transfers metrizability in the necessary direction; arbitrary injectivity or continuity alone would not suffice.

Used by: CantorCharacterization.nonempty_homeomorph_iff.

## Fixed local contracts

`HasClopenBasis X` is the literal basis of all clopen subsets. `BinaryScheme` fixes root, clopen and nonempty nodes, false/true disjoint covering children, and decision of basis member number `l.length` at each split. `next`, `addressPrefix`, and `code` remain fixed compared dependencies. Comparator definition_names is empty. The finite prefixes are reversed Bool lists, explicitly connected to PiNat.res.

## Mathlib/Topology/Defs/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean

SHA256 6a16294b9ce69e6f245f45abc59d45db011f2a1c545b4d5d403ccaca5b17c99c

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L71-L87

Excerpt SHA256 d0b4bb0467136b0769c0f64a370a326acdea032d7609448a0f7d8337b140031f

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L75-L110

Excerpt SHA256 32cd02dbee2407d6f2a2709782ad6b65bd88feb3a50558e4951344c640cfafd7

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L107-L109

Excerpt SHA256 b781df1f94b7e9a0b16791daa67c0bad5d4446809fc5e63093140999f5ae536a

```lean
class IsClosed (s : Set X) : Prop where
  /-- The complement of a closed set is an open set. -/
  isOpen_compl : IsOpen sᶜ
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L112-L113

Excerpt SHA256 d15fde9db9d1f1bc6c388a1d8f7c84eb3e0752449d0ac83bb8d07d893ce3f4dd

```lean
def IsClopen (s : Set X) : Prop :=
  IsClosed s ∧ IsOpen s
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L155-L158

Excerpt SHA256 338d6eb23853e428f3e57edbac5bae462158689cbbd74439f8cfa4cdbfd08e6b

```lean
structure Continuous (f : X → Y) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
```

## Mathlib/Data/Set/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean

SHA256 4b5433ba90d229d2875756f2c486de41e2e1b5be89b7255be5fe7ed2e0c524c7

```lean
/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L277-L281

Excerpt SHA256 cb3870fa0008d18792a7122276c41e3e45998a2f2defae575b4225f0a2cf53de

```lean
/-- The property `s.Nonempty` expresses the fact that the set `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def Nonempty (s : Set α) : Prop :=
  ∃ x, x ∈ s
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L266-L266

Excerpt SHA256 33bdb2da05833cc25b82686d5f94a98b24778577e5407ac386d980dd33e609a4

```lean
def image {β : Type v} (f : α → β) (s : Set α) : Set β := {f a | a ∈ s}
```

## Mathlib/Basic/Countable/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Countable/Defs.lean

SHA256 d42047c8b18f28b7eba8ceca5867e472fcb8e840ac3499f88d3cd1d01451bb9f

```lean
/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Countable/Defs.lean#L41-L46

Excerpt SHA256 551b5558571ec8d95682ed77589bddacda46501f10be4eef3efb6971e2a241e9

```lean
class Countable (α : Sort u) : Prop where
  /-- A type `α` is countable if there exists an injective map `α → ℕ`. -/
  exists_injective_nat' : ∃ f : α → ℕ, Injective f

lemma Countable.exists_injective_nat (α : Sort u) [Countable α] : ∃ f : α → ℕ, Injective f :=
  Countable.exists_injective_nat'
```

## Mathlib/Data/Set/Countable.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Countable.lean

SHA256 047d0f370cc830214b8dba702ec49434af0072523561404e40a314d2a5f24b98

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Countable.lean#L40-L49

Excerpt SHA256 029b5880e2f8d6ee503311ecdcfba5d91268eceeb5194b1788413175bcb3ccd5

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Countable.lean#L128-L135

Excerpt SHA256 9f910f7c565b48c923524f064214b8df96db7ea66273207d6a64f00608489b1a

```lean
/-- A non-empty set is countable iff there exists a surjection from the
natural numbers onto the subtype induced by the set.
-/
protected theorem countable_iff_exists_surjective {s : Set α} (hs : s.Nonempty) :
    s.Countable ↔ ∃ f : ℕ → s, Surjective f :=
  @countable_iff_exists_surjective s hs.to_subtype

alias ⟨Countable.exists_surjective, _⟩ := Set.countable_iff_exists_surjective
```

## Mathlib/Topology/Bases.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean

SHA256 fbd29cb53487d8ff54efda38cd831d4966a19a052654ef39a09352753986d1d6

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean#L793-L795

Excerpt SHA256 be0e6df4a04de8ef9819f4c545edf341efed762b08226cf4af131b90d05813b4

```lean
class _root_.SecondCountableTopology : Prop where
  /-- There exists a countable set of sets that generates the topology. -/
  is_open_generated_countable : ∃ b : Set (Set α), b.Countable ∧ t = TopologicalSpace.generateFrom b
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean#L73-L79

Excerpt SHA256 06ef0a524e711562ab10d1c840fe57620c7dd2df3111034ac2d8f81c0424ed42

```lean
structure IsTopologicalBasis (s : Set (Set α)) : Prop where
  /-- For every point `x`, the set of `t ∈ s` such that `x ∈ t` is directed downwards. -/
  exists_subset_inter : ∀ t₁ ∈ s, ∀ t₂ ∈ s, ∀ x ∈ t₁ ∩ t₂, ∃ t₃ ∈ s, x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂
  /-- The sets from `s` cover the whole space. -/
  sUnion_eq : ⋃₀ s = univ
  /-- The topology is generated by sets from `s`. -/
  eq_generateFrom : t = generateFrom s
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean#L797-L804

Excerpt SHA256 1d2bbba6b36e34e85c48c0bfe5c5d05b8b445469e9ff2228dad8646ac50518b3

```lean
protected theorem IsTopologicalBasis.secondCountableTopology {b : Set (Set α)}
    (hb : IsTopologicalBasis b) (hc : b.Countable) : SecondCountableTopology α :=
  ⟨⟨b, hc, hb.eq_generateFrom⟩⟩

lemma SecondCountableTopology.mk' {α} {b : Set (Set α)} (hc : b.Countable) :
    @SecondCountableTopology α (generateFrom b) :=
  @SecondCountableTopology.mk α (generateFrom b) ⟨b, hc, rfl⟩

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean#L811-L815

Excerpt SHA256 23a21589d0b5dab34322c819ed07e5a123b4b506ffdd168a2eb01177dc1e1af5

```lean
theorem exists_countable_basis [SecondCountableTopology α] :
    ∃ b : Set (Set α), b.Countable ∧ ∅ ∉ b ∧ IsTopologicalBasis b := by
  obtain ⟨b, hb₁, hb₂⟩ := @SecondCountableTopology.is_open_generated_countable α _ _
  refine ⟨_, ?_, notMem_sdiff_of_mem ?_, (isTopologicalBasis_of_subbasis hb₂).sdiff_empty⟩
  exacts [((countable_ofPred_finite_subset hb₁).image _).mono sdiff_subset, rfl]
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean#L930-L941

Excerpt SHA256 16328afa0beea669b91aaa80230b1d152898d3cf700e7213dc0a10ac60a211d1

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

## Mathlib/Topology/Order.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean

SHA256 2705ffc65ea519f775d4e9678578a2dbb18f096325f857c6267ac2bd83af86c5

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean#L62-L75

Excerpt SHA256 157d25ad393ea6c2266bed17f78f91f1658d33d3609091b788dfa8c70f0692a4

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean#L307-L311

Excerpt SHA256 26015841fe28c8608aba85513b1657bd58475e98010121e1391aeb8726391b3f

```lean
/-- A topological space is discrete if every set is open, that is,
  its topology equals the discrete topology `⊥`. -/
class DiscreteTopology (α : Type*) [t : TopologicalSpace α] : Prop where
  /-- The `TopologicalSpace` structure on a type with discrete topology is equal to `⊥`. -/
  eq_bot : t = ⊥
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Order.lean#L572-L576

Excerpt SHA256 2d8bbbaa7265a7f44dd244c394855aa4f2fccb8128ba008672e414bc4393a5d9

```lean
instance : DiscreteTopology PUnit := ⟨rfl⟩
instance : IndiscreteTopology PUnit := inferInstance

instance : TopologicalSpace Bool := ⊥
instance : DiscreteTopology Bool := ⟨rfl⟩
```

## Mathlib/Topology/Homeomorph/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Defs.lean

SHA256 4d27914014d20e4b9a6af97ebd7e7bea7451cc37a96dbd102b6d21c9a3f0eb72

```lean
/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Defs.lean#L42-L50

Excerpt SHA256 0b946359899cb78e8004065cc44729b505a4bff977bbf44444b74f5da935a5d4

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

SHA256 c75fb2a102be49010eac04a1602160eaaa2c4c18d12b29bf6f5c45f622dad1e8

```lean
/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Equiv/Defs.lean#L66-L77

Excerpt SHA256 6a1b835401ec07580608a00c5fa8b5085dd26fc6ee07dce4eaaa5f5fb26ad15d

```lean
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

## Mathlib/Logic/Function/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Function/Defs.lean

SHA256 a783ef2cbf8b63c895b371dfc43dec55fc07fee6bf0da23fa25cfbceab45a872

```lean
/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Haitao Zhang
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Function/Defs.lean#L162-L164

Excerpt SHA256 1c96641054d201c2db0c0ce991c137a931539b8fc41ed5e41360c0b2116d6c38

```lean
/-- A function is called bijective if it is both injective and surjective. -/
def Bijective (f : α → β) :=
  Injective f ∧ Surjective f
```

## Mathlib/Order/Disjoint.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Disjoint.lean

SHA256 5c59598e126b8345a9373277f8e30c0d52b3fce1080a96281f1dc54bc6dd619c

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Disjoint.lean#L48-L49

Excerpt SHA256 0afa2cf8eba8be7e8c79707dafde25b73970201e3d74bd9888afabf992c96ba2

```lean
def Disjoint (a b : α) : Prop :=
  ∀ ⦃x⦄, x ≤ a → x ≤ b → x ≤ ⊥
```

## Mathlib/Data/Set/Disjoint.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Disjoint.lean

SHA256 21e4643bfcae089dbbca262cb9d4b4bad1ad1cd77adf31ae43f4d2f2ab69e492

```lean
/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Disjoint.lean#L32-L33

Excerpt SHA256 6e2db5beb25dea053abf506750cca6f73c1641e037d9cb12976ccf586dcb2f7d

```lean
theorem disjoint_iff_inter_eq_empty : Disjoint s t ↔ s ∩ t = ∅ :=
  disjoint_iff
```

## Mathlib/Logic/Pairwise.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Pairwise.lean

SHA256 ccac95d1101a308ae38946e81caaa6d2c32e7e90ed99f7305dba9f01a955e62f

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Pairwise.lean#L33-L35

Excerpt SHA256 8ebaa32f0ec686f549223f6f457e93b9ab78c95dfb08e5968c891a6dde4af5eb

```lean
/-- A relation `r` holds pairwise if `r i j` for all `i ≠ j`. -/
def Pairwise (r : α → α → Prop) :=
  ∀ ⦃i j⦄, i ≠ j → r i j
```

## Mathlib/Data/Set/Operations.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean

SHA256 60e5fa9adbd7d068a553d5a28875f5250e0a20771b5179f9f552882d0865c68e

```lean
/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Johannes Hölzl, Reid Barton, Kim Morrison, Patrick Massot, Kyle Miller,
Minchao Wu, Yury Kudryashov, Floris van Doorn
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean#L135-L135

Excerpt SHA256 bdbb3311188d718892907fb87ac66f86bfb45fc4cbcefeb9b80864b388966258

```lean
def preimage (f : α → β) (s : Set β) : Set α := {x | f x ∈ s}
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean#L173-L173

Excerpt SHA256 6ea5f38bede17452fab4c6025aa7489ccb2b191c13d4a1ce86fc1d2bc8a6bbd0

```lean
def range (f : ι → α) : Set α := {x | ∃ y, f y = x}
```

## Mathlib/Topology/Defs/Induced.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean

SHA256 ba804ff6a2bd28aea83da56dfc339e565745a088d7aeac977643410f1dae8f74

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean#L64-L67

Excerpt SHA256 878b69c8488a10bac25ce164587ebbe29156ddb4fddd3fe1e9a3911d8bdd8110

```lean
def induced (f : X → Y) (t : TopologicalSpace Y) : TopologicalSpace X where
  IsOpen s := ∃ t, IsOpen t ∧ f ⁻¹' t = s
  isOpen_univ := ⟨univ, isOpen_univ, preimage_univ⟩
  isOpen_inter := by
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean#L145-L149

Excerpt SHA256 3298f2b98dd8701ecf141d8b2c58c7a3cd9312863c9cae9615d444bfad484a34

```lean
  and for all `s : Set X`, `s` is open iff it is the preimage of an open set. -/
@[fun_prop, mk_iff]
structure IsEmbedding (f : X → Y) : Prop extends IsInducing f where
  /-- A topological embedding is injective. -/
  injective : Function.Injective f
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean#L128-L134

Excerpt SHA256 884daae7f374977dffec6b6f379ec2bf9b884248d4f57b1b27710cefc5ac7110

```lean
/-- A function `f : X → Y` between topological spaces is inducing if the topology on `X` is induced
by the topology on `Y` through `f`, meaning that a set `s : Set X` is open iff it is the preimage
under `f` of some open set `t : Set Y`. -/
@[fun_prop, mk_iff]
structure IsInducing (f : X → Y) : Prop where
  /-- The topology on the domain is equal to the induced topology. -/
  eq_induced : tX = tY.induced f
```

## Mathlib/Topology/Constructions.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions.lean

SHA256 47de73fc60746ec4c31fa6e3fcb6d7fe8fbbcf5dbc88c0471fc017040a26467f

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions.lean#L66-L68

Excerpt SHA256 8d6d3bc58b2c45da4e5c3bc1a5c7df8aa12981d05fd20ae4735702d0dcaf5c76

```lean
instance Pi.topologicalSpace {ι : Type*} {Y : ι → Type v} [t₂ : (i : ι) → TopologicalSpace (Y i)] :
    TopologicalSpace ((i : ι) → Y i) :=
  ⨅ i, induced (fun f => f i) (t₂ i)
```

## Mathlib/Topology/MetricSpace/PiNat.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/PiNat.lean

SHA256 a6d5b738f8217038bc1b2889f5fa0f0ea84b544dbc21761e90b35dcf8cd0d669

```lean
/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/PiNat.lean#L109-L110

Excerpt SHA256 a45172b1a533ce6d7736a8b2d4709829b0a6c4ed21959e84070312d88432e511

```lean
def cylinder (x : ∀ n, E n) (n : ℕ) : Set (∀ n, E n) :=
  { y | ∀ i, i < n → y i = x i }
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/PiNat.lean#L195-L239

Excerpt SHA256 8ba98ec91cfb75501b47e742278333ac8844f08fe5e4c32aa10f2f905d1cb6bc

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/PiNat.lean#L344-L368

Excerpt SHA256 808b0ee14e623257bb1b10fd817064f716381635545a0bc70872163046b929c0

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/PiNat.lean#L191-L193

Excerpt SHA256 b7c50e4330d7be3ef49d1dbffb21714607d69decef6090de175e38a4106a39ae

```lean
def res (x : ℕ → α) : ℕ → List α
  | 0 => nil
  | Nat.succ n => x n :: res x n
```

## Mathlib/Topology/Defs/Filter.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean

SHA256 3b2ffc8154a531b4f0d3b36aa75ee08635c0df31884ba83baf1b0b0283c13748

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L293-L299

Excerpt SHA256 73972a6caa1a04dc4257f07a3dd4f189f937de1f64678b166a06806c12cd30d1

```lean
variable (X) in
/-- Type class for compact spaces. Separation is sometimes included in the definition, especially
in the French literature, but we do not include it here. -/
@[wikidata Q381892]
class CompactSpace : Prop where
  /-- In a compact space, `Set.univ` is a compact set. -/
  isCompact_univ : IsCompact (Set.univ : Set X)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L283-L286

Excerpt SHA256 5b9c87379963ecd9b39f25869d8dfe0aa53e9861b3cd97fb69cfcb94ae036548

```lean
/-- A point `x` is an accumulation point of a filter `F` if `𝓝[≠] x ⊓ F ≠ ⊥`.
See also `ClusterPt`. -/
def AccPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝[≠] x ⊓ F)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L136-L146

Excerpt SHA256 66d257ee2991366f209610ee7cf88410147833a0310b171216f8690f86f8b42c

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L221-L222

Excerpt SHA256 e809956c5dea068e27b679d8ffde1bd9afd081fcc514ea99d45dd53014ee5b1b

```lean
def Inseparable (x y : X) : Prop :=
  𝓝 x = 𝓝 y
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L288-L291

Excerpt SHA256 8a5dd611ce1298df5a9753168f4f6cd3dc9f56e66212e62e0043a0dcae9c2833

```lean
/-- A set `s` is compact if for every nontrivial filter `f` that contains `s`,
there exists `a ∈ s` such that every set of `f` meets every neighborhood of `a`. -/
def IsCompact (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L271-L276

Excerpt SHA256 82c9fd0900d0a55fa46c6a78fa400334fd5b57e606aa9b7c35a3fb022fe2398b

```lean
/-- A point `x` is a cluster point of a filter `F` if `𝓝 x ⊓ F ≠ ⊥`.
Also known as an accumulation point or a limit point, but beware that terminology varies.
This is *not* the same as asking `𝓝[≠] x ⊓ F ≠ ⊥`, which is called `AccPt` in Mathlib.
See `mem_closure_iff_clusterPt` in particular. -/
def ClusterPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝 x ⊓ F)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L127-L134

Excerpt SHA256 50aa67ca57c8473255d83882eea110cc29269ae9a77d58cae57886b24f0bfa07

```lean
/-- A set is called a neighborhood of `x` if it contains an open set around `x`. The set of all
neighborhoods of `x` forms a filter, the neighborhood filter at `x`, is here defined as the
infimum over the principal filters of all open sets containing `x`. -/
irreducible_def nhds (x : X) : Filter X :=
  ⨅ s ∈ { s : Set X | x ∈ s ∧ IsOpen s }, 𝓟 s

@[inherit_doc]
scoped[Topology] notation "𝓝" => nhds
```

## Mathlib/Topology/Perfect.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Perfect.lean

SHA256 40c4a61f6a8a9f923674520215130f4ffd77ba4f69fb8ee0ba5ed5d461637f7f

```lean
/-
Copyright (c) 2022 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Perfect.lean#L95-L105

Excerpt SHA256 00b86428446eabdad2c97a72547e797e4fd199f5db6f5e06826e9065fc5b0040

```lean

/--
A topological space `X` is said to be perfect if its universe is a perfect set.
Equivalently, this means that `𝓝[≠] x ≠ ⊥` for every point `x : X`.
-/
@[mk_iff perfectSpace_def]
class PerfectSpace : Prop where
  univ_preperfect : Preperfect (Set.univ : Set α)

theorem PerfectSpace.univ_perfect [PerfectSpace α] : Perfect (Set.univ : Set α) :=
  ⟨isClosed_univ, PerfectSpace.univ_preperfect⟩
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Perfect.lean#L74-L79

Excerpt SHA256 aa7ae39eb772dafd5d7b7ac452755a640a1a7635631bcfe69929b17277f7dee1

```lean

/-- A set `C` is preperfect if all of its points are accumulation points of itself.
If `α` is a T1 space, this is equivalent to the closure of `C` being perfect,
see `preperfect_iff_perfect_closure`. This property is also called dense-in-itself. -/
def Preperfect (C : Set α) : Prop :=
  ∀ x ∈ C, AccPt x (𝓟 C)
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Perfect.lean#L89-L90

Excerpt SHA256 b912ef934d8f2daa8aec935c6523fffe38d671c447af8f22096488869ba76b5c

```lean
theorem preperfect_iff_nhds : Preperfect C ↔ ∀ x ∈ C, ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ C, y ≠ x := by
  simp only [Preperfect, accPt_iff_nhds]
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Perfect.lean#L278-L282

Excerpt SHA256 2811b3b4b48c879eb097a6e8ab2f80982d32b9f0c1b6701da4545fd5994f752e

```lean
theorem perfectSpace_iff_forall_not_isolated : PerfectSpace X ↔ ∀ x : X, Filter.NeBot (𝓝[≠] x) := by
  simp [perfectSpace_def, Preperfect, AccPt]

instance PerfectSpace.not_isolated [PerfectSpace X] (x : X) : Filter.NeBot (𝓝[≠] x) :=
  perfectSpace_iff_forall_not_isolated.mp ‹_› x
```

## Mathlib/Topology/ClusterPt.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/ClusterPt.lean

SHA256 97256f9659e179ee0327e4601d3d1e01b520f0d5b8981849a0cd0d97b907c848

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/ClusterPt.lean#L206-L210

Excerpt SHA256 24289dc8d07c4af661c4be5df6af99dc0265f368b767507d1cd69191cb73d6b6

```lean
theorem accPt_iff_nhds {x : X} {C : Set X} : AccPt x (𝓟 C) ↔ ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ C, y ≠ x := by
  simp [accPt_principal_iff_clusterPt, clusterPt_principal_iff, Set.Nonempty,
    and_assoc]

/-- `x` is an accumulation point of a set `C` iff
```

## Mathlib/Topology/Separation/Hausdorff.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/Hausdorff.lean

SHA256 95c58f7ad7ef3ea627d5af8d2427c7d7e08a47207ed084e51945217f32566f06

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/Hausdorff.lean#L81-L91

Excerpt SHA256 e875f4f7c4e62052292e8ce7f9e0caac25e7dd18a47fc9e6dec7240de02cdd81

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

## Mathlib/Topology/Separation/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/Basic.lean

SHA256 96c74f410b14c3adecc1cb06d90d9d7a61bbb1529c18000426687bee99ba6991

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/Basic.lean#L73-L82

Excerpt SHA256 b81e09d464c3afc469981bac9cd9928ef560a856c89e9af4ad91e999a5dfd68b

```lean
/-- A T₀ space, also known as a Kolmogorov space, is a topological space such that for every pair
`x ≠ y`, there is an open set containing one but not the other. We formulate the definition in terms
of the `Inseparable` relation. -/
@[stacks 004X "(2)"]
class T0Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Two inseparable points in a T₀ space are equal. -/
  t0 : ∀ ⦃x y : X⦄, Inseparable x y → x = y

theorem t0Space_iff_inseparable (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ ∀ x y : X, Inseparable x y → x = y :=
```

## Mathlib/Topology/Metrizable/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/Basic.lean

SHA256 b3109255e290e85cfeaca128a66def49978c4e9fe22866c499e9882132bd3ac8

```lean
/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/Basic.lean#L115-L137

Excerpt SHA256 b719f45659b428eea69ab09ffa5ff7f2f7617ee399d7c9a128b83242c0d16a5f

```lean
    ⟨⊤, (IndiscreteTopology.eq_top X).symm, isCountablyGenerated_top⟩

/-- A topological space is metrizable if there exists a metric space structure compatible with the
topology. To minimize imports, we implement this class in terms of the existence of a
countably generated uniformity inducing the topology, which is mathematically
equivalent.
To endow such a space with a compatible uniformity, use
`letI : UniformSpace X := TopologicalSpace.pseudoMetrizableSpaceUniformity X`.
To endow such a space with a compatible distance, use
`letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X`. -/
class MetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop extends
    PseudoMetrizableSpace X, T0Space X

-- See note [lower instance priority]
attribute [instance 100] MetrizableSpace.toT0Space
attribute [instance 100] MetrizableSpace.toPseudoMetrizableSpace

instance (priority := 100) PseudoMetrizableSpace.toMetrizableSpace
    [T0Space X] [h : PseudoMetrizableSpace X] : MetrizableSpace X where

instance (priority := 100) t2Space_of_metrizableSpace [MetrizableSpace X] : T2Space X :=
  letI : UniformSpace X := pseudoMetrizableSpaceUniformity X
  inferInstance
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/Basic.lean#L34-L45

Excerpt SHA256 a48d22cf7db086b8bc2a9d909ba5232b909274df228c82ed3e31cad87c86bf4d

```lean
/-- A topological space is *pseudometrizable* if there exists a pseudometric space structure
compatible with the topology. To minimize imports, we implement this class in terms of the
existence of a countably generated uniformity inducing the topology, which is mathematically
equivalent.
To endow such a space with a compatible uniformity, use
`letI : UniformSpace X := TopologicalSpace.pseudoMetrizableSpaceUniformity X`.
To endow such a space with a compatible distance, use
`letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X`. -/
class PseudoMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  exists_countably_generated :
    ∃ u : UniformSpace X, u.toTopologicalSpace = t ∧ (uniformity X).IsCountablyGenerated

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/Basic.lean#L166-L176

Excerpt SHA256 2cf83c5b9270afe92b3918d6ea38f9b303e553b630aa076488a204bb0496a800

```lean
instance (X : Type*) [TopologicalSpace X] [LindelofSpace X] [PseudoMetrizableSpace X] :
    SecondCountableTopology X := by
  let := pseudoMetrizableSpaceUniformity X
  have := pseudoMetrizableSpaceUniformity_countably_generated X
  suffices _ : SeparableSpace X from secondCountable_of_separable X
  obtain ⟨V, hVb, hVs⟩ := has_seq_basis X
  choose U hUc hUu using fun n =>
    LindelofSpace.elim_nhds_subcover (fun x => ball x (V n))
      (fun x => ball_mem_nhds x (hVb.mem n))
  refine ⟨Set.iUnion U, Set.countable_iUnion hUc, fun x => ?_⟩
  rw [mem_closure_iff_frequently, nhds_eq_comap_uniformity, frequently_comap, hVb.frequently_iff]
```

## Mathlib/Order/Filter/CountablyGenerated.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/CountablyGenerated.lean

SHA256 5628113472da223e2345cc12426ec269ca87c2e233eb76e9789ed1c21719f2d0

```lean
/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Yury Kudryashov, Patrick Massot
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/CountablyGenerated.lean#L29-L32

Excerpt SHA256 049037e8cae993a87f04992fca2c9d4ab8212a0bb6e0c9f8b0f172c304148b79

```lean
/-- `IsCountablyGenerated f` means `f = generate s` for some countable `s`. -/
class IsCountablyGenerated (f : Filter α) : Prop where
  /-- There exists a countable set that generates the filter. -/
  out : ∃ s : Set (Set α), s.Countable ∧ f = generate s
```

## Mathlib/Order/Filter/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Basic.lean

SHA256 5dac9f84ef61915588e250fbb6e816ecf3d3183a94aa7e31f85e390baeb30afb

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Basic.lean#L163-L174

Excerpt SHA256 5d01aff6d8f48d930b9443ba3824e8437c572ea18bd4320278310d9ce3018cc4

```lean
inductive GenerateSets (g : Set (Set α)) : Set α → Prop
  | basic {s : Set α} : s ∈ g → GenerateSets g s
  | univ : GenerateSets g univ
  | superset {s t : Set α} : GenerateSets g s → s ⊆ t → GenerateSets g t
  | inter {s t : Set α} : GenerateSets g s → GenerateSets g t → GenerateSets g (s ∩ t)

/-- `generate g` is the largest filter containing the sets `g`. -/
def generate (g : Set (Set α)) : Filter α where
  sets := {s | GenerateSets g s}
  univ_sets := GenerateSets.univ
  sets_of_superset := GenerateSets.superset
  inter_sets := GenerateSets.inter
```

## Mathlib/Topology/Metrizable/Uniformity.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/Uniformity.lean

SHA256 57cd395dfc2492244906b4cd136ca48bf553fca053e5fdb3033132f105a7d265

```lean
/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Metrizable/Uniformity.lean#L264-L283

Excerpt SHA256 dbb69ab5348ec0bf4d6afd06e69488c778b32499c2c3024a7e5343ddfd6db56d

```lean
-- see note [reducible non-instances]
noncomputable abbrev TopologicalSpace.pseudoMetrizableSpacePseudoMetric (X : Type*)
    [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] : PseudoMetricSpace X :=
  letI := TopologicalSpace.pseudoMetrizableSpaceUniformity X
  haveI := TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated X
  UniformSpace.pseudoMetricSpace X

example {X : Type*} [t : TopologicalSpace X] [t.PseudoMetrizableSpace] :
    t.pseudoMetrizableSpacePseudoMetric.toUniformSpace = t.pseudoMetrizableSpaceUniformity := by
  with_reducible_and_instances rfl

/-- Construct on a metrizable space a metric compatible with the topology. -/
noncomputable abbrev TopologicalSpace.metrizableSpaceMetric (X : Type*) [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] : MetricSpace X :=
  letI := pseudoMetrizableSpacePseudoMetric X
  .ofT0PseudoMetricSpace X

example {X : Type*} [t : TopologicalSpace X] [t.MetrizableSpace] :
    t.metrizableSpaceMetric.toPseudoMetricSpace = t.pseudoMetrizableSpacePseudoMetric := by
  with_reducible_and_instances rfl
```

## Mathlib/Order/Filter/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean

SHA256 d0b1e4022a3910b2768e8786a3a66d701db0cb4c59c055b3bd17ec4cd28a60e5

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L267-L277

Excerpt SHA256 de28aba95e4d9fbf3ff965f6b2efbc6b1591d5b15e59c8422eefe58ba95c15ad

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L71-L83

Excerpt SHA256 0d537bbb0e92a3e5a1c9a1c33b713a8c1351c8f23d9b835133dba47b1c526200

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L147-L158

Excerpt SHA256 b9ac7078f265922dbe9c103f5320642c8b0341f855d674b959a051d39edcee33

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L405-L423

Excerpt SHA256 e6f89a53ff1df261c7705955e27a8d227354e5926f369e20b02c35ad98be4313

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L425-L439

Excerpt SHA256 362366ce36802bc59b3b10b58727f2c6636d06fcf2d31241e21f8d26a375d782

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L183-L190

Excerpt SHA256 a99ab18fd794b2e2b76c56bfa8532bcb16e403417f304a87285b776cb5782aca

```lean
  le f g := ∀ ⦃U : Set α⦄, U ∈ g → U ∈ f
  le_antisymm a b h₁ h₂ := filter_eq <| Subset.antisymm h₂ h₁
  le_refl a := Subset.rfl
  le_trans a b c h₁ h₂ := Subset.trans h₂ h₁

theorem le_def : f ≤ g ↔ ∀ x ∈ g, x ∈ f :=
  Iff.rfl

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/Defs.lean#L444-L452

Excerpt SHA256 9ef3719fef82cd6404287f98980c3054bbce035b372a7bd938e80fccdc056a78

```lean
/-- Product of filters. This is the filter generated by Cartesian products
of elements of the component filters. -/
instance instSProd : SProd (Filter α) (Filter β) (Filter (α × β)) where
  sprod f g := f.comap Prod.fst ⊓ g.comap Prod.snd

theorem prod_eq_inf (f : Filter α) (g : Filter β) : f ×ˢ g = f.comap Prod.fst ⊓ g.comap Prod.snd :=
  rfl

/-- The product of an indexed family of filters. -/
```

## Mathlib/Topology/Compactness/Compact.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Compact.lean

SHA256 3fc7ffe7db4db0a2de07d6fdf0e65da486b3dced1f3bac4d58ab869a92f4ac64

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Compact.lean#L336-L346

Excerpt SHA256 39d0f9e050fc50eeda72d8bc66e1d8cefcb02f7ffc8c11094fe166101d16ee37

```lean
/-- Cantor's intersection theorem for sequences indexed by `ℕ`:
the intersection of a decreasing sequence of nonempty compact closed sets is nonempty. -/
theorem IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (t : ℕ → Set X)
    (htd : ∀ i, t (i + 1) ⊆ t i) (htn : ∀ i, (t i).Nonempty) (ht0 : IsCompact (t 0))
    (htcl : ∀ i, IsClosed (t i)) : (⋂ i, t i).Nonempty :=
  have tmono : Antitone t := antitone_nat_of_succ_le htd
  have htd : Directed (· ⊇ ·) t := tmono.directed_ge
  have : ∀ i, t i ⊆ t 0 := fun i => tmono <| Nat.zero_le i
  have htc : ∀ i, IsCompact (t i) := fun i => ht0.of_isClosed_subset (htcl i) (this i)
  IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn htc htcl

```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Compact.lean#L384-L389

Excerpt SHA256 a48a11009a0c741b08d427892ef7d163ea7c6e21e3dd43a265d6ce8ee7149a11

```lean
/-- A set `s` is compact if and only if
for every open cover of `s`, there exists a finite subcover. -/
theorem isCompact_iff_finite_subcover :
    IsCompact s ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) → ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  ⟨fun hs => hs.elim_finite_subcover, isCompact_of_finite_subcover⟩
```

## Mathlib/Topology/Homeomorph/Lemmas.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Lemmas.lean

SHA256 e76ff3b356c5cff8dafa5ebdb561b7f439ad7d687e0def918e6512e36ef02e9e

```lean
/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Homeomorph/Lemmas.lean#L469-L477

Excerpt SHA256 224f9c67092a3b7828360ddd3608d23f326e0f67a233b3544c24dac80aeeb6e8

```lean
/-- Continuous equivalences from a compact space to a T2 space are homeomorphisms.

This is not true when T2 is weakened to T1
(see `Continuous.homeoOfEquivCompactToT2.t1_counterexample`). -/
@[simps toEquiv]
def homeoOfEquivCompactToT2 [CompactSpace X] [T2Space Y] {f : X ≃ Y} (hf : Continuous f) : X ≃ₜ Y :=
  { f with
    continuous_toFun := hf
    continuous_invFun := hf.continuous_symm_of_equiv_compact_to_t2 }
```

## Mathlib/Topology/UniformSpace/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean

SHA256 0678d9754b2f7c95f4ca1c62ff0fe923bfff83092e890b26d524040be1f1a47c

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean#L185-L209

Excerpt SHA256 a67f56908a4cffd4c4c069fff92e9f5256c8d56e81e6c5e074c827feac86bc13

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/UniformSpace/Defs.lean#L129-L140

Excerpt SHA256 5313987700fb612d91a82f7603e0ae3fe6cda1b5d64773c26afedb74c7f1bb37

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

SHA256 ef0e4d65986641366ffcc380a613f210207fee31e8640e1488a8cae41395383a

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Neighborhoods.lean#L64-L66

Excerpt SHA256 3920d4125f26e7f74ea0eb050f41fa4c4f00ef056b57524cd6b93066efb1d515

```lean
theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t :=
  (nhds_basis_opens x).mem_iff.trans <| exists_congr fun _ =>
    ⟨fun h => ⟨h.2, h.1.2, h.1.1⟩, fun h => ⟨⟨h.2.2, h.2.1⟩, h.1⟩⟩
```

## Pinned compiler primitives

Exact compiler commit `11acb17ec6b07a8f9e9173e6845197929540936b`. These core excerpts are retained here separately from the Mathlib-only consistency schema. Nonempty is existence of an element of a sort; Injective means equal images force equal inputs; Surjective means every target is attained. Neither compactness nor PerfectSpace excludes Empty by itself.

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Function.lean#L59-L63

Full source SHA256 88217ed8ec91da1ec655c8a10f737b659a4570b4c05dbd6b084162a3157cf030

Excerpt SHA256 81f3c1294b8b4f215a4b094823922dbd95234cd6a53280e94f6fd6d7280c0148

```lean
/-- A function `f : α → β` is called surjective if every `b : β` is equal to `f a`
for some `a : α`. -/
@[expose]
def Surjective (f : α → β) : Prop :=
  ∀ b, Exists fun a => f a = b
```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean#L839-L841

Full source SHA256 cc9f337a5d8bd00768121701bceb0661ac63e01831a9aa34b282f37c689a6c39

Excerpt SHA256 409b9d791b14a599f13bb14741bdfbfc112bc04bd4fc41d9924083fa47df7598

```lean
class inductive Nonempty (α : Sort u) : Prop where
  /-- If `val : α`, then `α` is nonempty. -/
  | intro (val : α) : Nonempty α
```

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/Function.lean#L49-L55

Full source SHA256 88217ed8ec91da1ec655c8a10f737b659a4570b4c05dbd6b084162a3157cf030

Excerpt SHA256 36854a442e2582f69c6ccd6a3faa453d39476628568d5e6b369e592ca31db3c3

```lean
  rfl

/-- A function `f : α → β` is called injective if `f x = f y` implies `x = y`. -/
@[expose]
def Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

```
