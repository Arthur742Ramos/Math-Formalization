# Pinned definitions and hypothesis audit

This package uses the exact Mathlib lockfile revision `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
The following retained definitions make every material topological hypothesis and
conclusion of the six selected contracts auditable without relying on moving docs.
Source-file and literal-excerpt hashes and upstream Apache attribution are retained
below and in `verification/material-imported-definitions.json`.

## Contract scope

| Selected result | Hypotheses and boundaries |
| --- | --- |
| exists_maximal_pairwiseDisjoint_refinement | Arbitrary type X, independent label universe, f and admissibility P. No topology or nonempty premise; maximal under inclusion among admissible label families. |
| exists_pairwiseDisjoint_dense_refinement | Topology on X, open G, admissible images open/nonempty/subsets of G, and refinement of each nonempty open part of G. G may be empty. Relative density G subset closure of the union; no countable-size bound. |
| exists_dense_isGdelta_fiber_witness | Baire X, locally compact R1 Y, a sequence of dense open product sets, fixed nonempty open V. The dense Gdelta parameter witness depends on D and V. It gives a fiber point for every parameter in that witness, not dense entire sections. |
| exists_dense_isGdelta_subset_image_fst | Same space hypotheses; D is a dense Gdelta of the actual product topology, V fixed open/nonempty. First projection restricted to V contains a dense Gdelta parameter set. |
| baireSpace_prod | Baire X and locally compact R1 Y imply the actual product is Baire. No separation, countability, regularity or nonempty assumption on X; no separate Baire Y hypothesis. |
| baireSpace_prod_of_compact | Baire X and compact R1 Y. Compact supplies weak local compactness; R1 upgrades it to the required local compactness convention. |

X and Y have independent Lean universes. Empty factors are allowed in the product
theorems. In the projection statements V.Nonempty entails an inhabited fiber region;
when Y is empty that premise is impossible. No global Nonempty instance is silently
added. No one parameter set for all fiber regions, full pseudocomplete theorem or
unrestricted product of Baire spaces is asserted.

## Literal predicates, class wrappers and proved bridges

### BaireSpace

Every natural-number-indexed intersection of dense open sets is dense. No separation or nonempty hypothesis.

The class field uses Dense and IsOpen in the given topology, including the canonical product topology for the conclusions.

Bridge kind: `class-fields`. Class wrappers use constructor/projection proofs, never `Iff.rfl`. Literal definitional unfolding and further proved characterizations are distinguished in the independently imported test modules.

Selected uses:

- `LocallyCompactBaire.exists_dense_isGdelta_fiber_witness`
- `LocallyCompactBaire.exists_dense_isGdelta_subset_image_fst`
- `LocallyCompactBaire.baireSpace_prod`
- `LocallyCompactBaire.baireSpace_prod_of_compact`

### R1Space

Preregular: topologically distinguishable points have disjoint neighborhood filters. R1 does not imply T0 or Hausdorff.

Literal field is Specializes x y or disjoint neighborhood filters. Specializes is neighborhood-filter order; the inseparable alternative is a proved equivalence.

Bridge kind: `class-fields`. Class wrappers use constructor/projection proofs, never `Iff.rfl`. Literal definitional unfolding and further proved characterizations are distinguished in the independently imported test modules.

Selected uses:

- `LocallyCompactBaire.exists_dense_isGdelta_fiber_witness`
- `LocallyCompactBaire.exists_dense_isGdelta_subset_image_fst`
- `LocallyCompactBaire.baireSpace_prod`
- `LocallyCompactBaire.baireSpace_prod_of_compact`

### LocallyCompactSpace

Every neighborhood of every point contains a compact neighborhood of that point.

This is the full compact-neighborhood-basis convention, not merely existence of one compact neighborhood. Compactness means IsCompact without separation.

Bridge kind: `class-fields`. Class wrappers use constructor/projection proofs, never `Iff.rfl`. Literal definitional unfolding and further proved characterizations are distinguished in the independently imported test modules.

Selected uses:

- `LocallyCompactBaire.exists_dense_isGdelta_fiber_witness`
- `LocallyCompactBaire.exists_dense_isGdelta_subset_image_fst`
- `LocallyCompactBaire.baireSpace_prod`

### CompactSpace

The whole space is IsCompact, without a bundled Hausdorff or nonempty assumption.

CompactSpace gives WeaklyLocallyCompactSpace. R1 permits upgrading this to LocallyCompactSpace in the compact specialization.

Bridge kind: `class-fields`. Class wrappers use constructor/projection proofs, never `Iff.rfl`. Literal definitional unfolding and further proved characterizations are distinguished in the independently imported test modules.

Selected uses:

- `LocallyCompactBaire.baireSpace_prod_of_compact`

### IsCompact

Every nontrivial filter supported on the set has a cluster point in that set.

ClusterPt x f means the meet of the neighborhood filter at x and f is nontrivial. Under R1 the closure of an IsCompact set is compact, not necessarily equal to the original set.

Bridge kind: `literal-unfolding`. Class wrappers use constructor/projection proofs, never `Iff.rfl`. Literal definitional unfolding and further proved characterizations are distinguished in the independently imported test modules.

Selected uses:

- `LocallyCompactBaire.exists_dense_isGdelta_fiber_witness`
- `LocallyCompactBaire.exists_dense_isGdelta_subset_image_fst`
- `LocallyCompactBaire.baireSpace_prod`
- `LocallyCompactBaire.baireSpace_prod_of_compact`

### Dense

Every ambient point belongs to the closure; equivalently every nonempty open set meets the set.

Closure is the intersection of all closed supersets. The open-intersection characterization is proved, not literal unfolding.

Bridge kind: `literal-unfolding`. Class wrappers use constructor/projection proofs, never `Iff.rfl`. Literal definitional unfolding and further proved characterizations are distinguished in the independently imported test modules.

Selected uses:

- `LocallyCompactBaire.exists_dense_isGdelta_fiber_witness`
- `LocallyCompactBaire.exists_dense_isGdelta_subset_image_fst`

### IsGδ

A countable family of open sets has the given set as its intersection.

The literal definition uses a countable set of sets. A natural-number-indexed open-intersection representation is a proved equivalence, including the empty family.

Bridge kind: `literal-unfolding`. Class wrappers use constructor/projection proofs, never `Iff.rfl`. Literal definitional unfolding and further proved characterizations are distinguished in the independently imported test modules.

Selected uses:

- `LocallyCompactBaire.exists_dense_isGdelta_fiber_witness`
- `LocallyCompactBaire.exists_dense_isGdelta_subset_image_fst`

### Set.PairwiseDisjoint

For every pair of distinct labels in the chosen family, their image sets are disjoint.

Set.Pairwise quantifies distinct labels; Disjoint on sets means empty intersection. Equal inhabited image sets are not exempt. No countability or universe identification is added.

Bridge kind: `literal-unfolding`. Class wrappers use constructor/projection proofs, never `Iff.rfl`. Literal definitional unfolding and further proved characterizations are distinguished in the independently imported test modules.

Selected uses:

- `LocallyCompactBaire.exists_maximal_pairwiseDisjoint_refinement`
- `LocallyCompactBaire.exists_pairwiseDisjoint_dense_refinement`

### IsOpen

The open-set predicate supplied by the given ambient topological-space structure.

TopologicalSpace supplies the open-set axioms. IsOpen literally projects its protected field; the actual product topology is the infimum of the two coordinate-induced topologies.

Bridge kind: `literal-unfolding`. Class wrappers use constructor/projection proofs, never `Iff.rfl`. Literal definitional unfolding and further proved characterizations are distinguished in the independently imported test modules.

Selected uses:

- `LocallyCompactBaire.exists_pairwiseDisjoint_dense_refinement`
- `LocallyCompactBaire.exists_dense_isGdelta_fiber_witness`
- `LocallyCompactBaire.exists_dense_isGdelta_subset_image_fst`

### closure

The smallest closed superset: the intersection of every closed set containing the given set.

This term appears in the dense-refinement conclusion G subset closure of the union. IsClosed is the open-complement class; closure is not a compactness or Hausdorff assumption.

Bridge kind: `literal-unfolding`. Class wrappers use constructor/projection proofs, never `Iff.rfl`. Literal definitional unfolding and further proved characterizations are distinguished in the independently imported test modules.

Selected uses:

- `LocallyCompactBaire.exists_pairwiseDisjoint_dense_refinement`

## Proof-critical dependency chain and source-fidelity limits

The rectangle construction carries `TopologicalSpace.PositiveCompacts`, extending
`Compacts` by nonempty interior. Its open sets live in X; shrinking closures occurs
only in Y. The R1 section supplies compactness of compact-set closures and containment
of those closures in any open superset. It does not say compact subsets are closed.
Positive-compact shrinking and the decreasing nonempty closed-set intersection theorem
are retained below with the relevant R1 and weak-local context. The intersection
theorem needs only compactness of its first set and closedness of every set, and
does not add a Hausdorff assumption. Product Baireness is obtained after the fiber
construction; it is not assumed by that construction.

The indexed disjointness definition is authoritative. The overview sentence in the
upstream pairwise-disjoint file about images being either equal or disjoint is not
the selected indexed contract: distinct labels with equal inhabited images cannot
both belong to the chosen family. The existing semantic counterexample checks this.

These are canonical topological and set-theoretic notions; no project-specific
replacement predicate is substituted. Elementary membership, subset, natural-number
intersection and actual product topology retain their ordinary Lean/Mathlib meanings.
The inventory targets material contract predicates and the critical proof chain,
not every transitive imported declaration. Independent review owns completeness
and mathematical interpretation; hashes and static checks do not certify either.
Separate Challenge and Solution tests check the listed meanings, R1 compact closure,
positive compact shrinking and closed nested intersections under the stated premises.
Source adaptation to Aarts–Lutzer Section4.1 and its explicit arbitrary-X/R1 assumptions,
and Li–Zsilinszky research context, remain as stated in README and metadata. No novelty,
unconsulted-original proof correspondence or editorial acceptance is inferred.

## Retained exact upstream source

### Mathlib/Topology/Defs/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean

File SHA256: `6a16294b9ce69e6f245f45abc59d45db011f2a1c545b4d5d403ccaca5b17c99c`

Git blob: `326105821a5a8ce5041ccf8dce22779bd55fa923`

License: Apache-2.0. Retained upstream header:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

#### topology-open-closed

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

#### interior-closure

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

#### Dense

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L145-L147

Excerpt SHA256: `2a52522d35b48a1b96df7fa73b15254b113108436e633e0e45e5bdffc455fbf8`

```lean
/-- A set is dense in a topological space if every point belongs to its closure. -/
def Dense (s : Set X) : Prop :=
  ∀ x, x ∈ closure s
```

#### BaireSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L235-L240

Excerpt SHA256: `977d5c7b2d9473e369aa9c2df40a2da2bea81bf7fb22f4978096b547f603e335`

```lean
/-- The property `BaireSpace α` means that the topological space `α` has the Baire property:
any countable intersection of open dense subsets is dense.
Formulated here when the source space is ℕ.
Use `dense_iInter_of_isOpen` which works for any countable index type instead. -/
class BaireSpace (X : Type*) [TopologicalSpace X] : Prop where
  baire_property : ∀ f : ℕ → Set X, (∀ n, IsOpen (f n)) → (∀ n, Dense (f n)) → Dense (⋂ n, f n)
```

### Mathlib/Topology/Defs/Filter.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean

File SHA256: `3b2ffc8154a531b4f0d3b36aa75ee08635c0df31884ba83baf1b0b0283c13748`

Git blob: `343fd3e5f576a8e0f0f040eb2df8e5c309106655`

License: Apache-2.0. Retained upstream header:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

#### filter-context

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L122-L125

Excerpt SHA256: `f0d097b9088681bc9b24ae95010a381fe6ec5d223ad9bdd58157cef20eaac984`

```lean
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

open Filter
open scoped Topology
```

#### nhds

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

#### Specializes

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L193-L210

Excerpt SHA256: `9ba7a645add0aca2d044eb709cb5b59c270536d761af1ec8b27957edb2f05f33`

```lean

/-- `x` specializes to `y` (notation: `x ⤳ y`) if either of the following equivalent properties
hold:

* `𝓝 x ≤ 𝓝 y`; this property is used as the definition;
* `pure x ≤ 𝓝 y`; in other words, any neighbourhood of `y` contains `x`;
* `y ∈ closure {x}`;
* `closure {y} ⊆ closure {x}`;
* for any closed set `s` we have `x ∈ s → y ∈ s`;
* for any open set `s` we have `y ∈ s → x ∈ s`;
* `y` is a cluster point of the filter `pure x = 𝓟 {x}`.

This relation defines a `Preorder` on `X`. If `X` is a T₀ space, then this `Preorder` is a
`PartialOrder`. If `X` is a T₁ space, then this `PartialOrder` is trivial: `x ⤳ y ↔ x = y`. -/
def Specializes (x y : X) : Prop := 𝓝 x ≤ 𝓝 y

@[inherit_doc]
infixl:300 " ⤳ " => Specializes
```

#### Inseparable

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L212-L222

Excerpt SHA256: `84057f5ddefc324abe61ece92b2d183791f2743889fe3e5fbb4e6fad734a36ea`

```lean
/-- Two points `x` and `y` in a topological space are `Inseparable`, or *topologically
indistinguishable*, if any of the following equivalent properties hold:

- `𝓝 x = 𝓝 y`; we use this property as the definition;
- for any open set `s`, `x ∈ s ↔ y ∈ s`, see `inseparable_iff_forall_isOpen`;
- for any closed set `s`, `x ∈ s ↔ y ∈ s`, see `inseparable_iff_forall_isClosed`;
- `x ∈ closure {y}` and `y ∈ closure {x}`, see `inseparable_iff_mem_closure`;
- `closure {x} = closure {y}`, see `inseparable_iff_closure_eq`.
-/
def Inseparable (x y : X) : Prop :=
  𝓝 x = 𝓝 y
```

#### ClusterPt

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L271-L276

Excerpt SHA256: `82c9fd0900d0a55fa46c6a78fa400334fd5b57e606aa9b7c35a3fb022fe2398b`

```lean
/-- A point `x` is a cluster point of a filter `F` if `𝓝 x ⊓ F ≠ ⊥`.
Also known as an accumulation point or a limit point, but beware that terminology varies.
This is *not* the same as asking `𝓝[≠] x ⊓ F ≠ ⊥`, which is called `AccPt` in Mathlib.
See `mem_closure_iff_clusterPt` in particular. -/
def ClusterPt (x : X) (F : Filter X) : Prop :=
  NeBot (𝓝 x ⊓ F)
```

#### IsCompact

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L288-L291

Excerpt SHA256: `8a5dd611ce1298df5a9753168f4f6cd3dc9f56e66212e62e0043a0dcae9c2833`

```lean
/-- A set `s` is compact if for every nontrivial filter `f` that contains `s`,
there exists `a ∈ s` such that every set of `f` meets every neighborhood of `a`. -/
def IsCompact (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f
```

#### CompactSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L293-L299

Excerpt SHA256: `73972a6caa1a04dc4257f07a3dd4f189f937de1f64678b166a06806c12cd30d1`

```lean
variable (X) in
/-- Type class for compact spaces. Separation is sometimes included in the definition, especially
in the French literature, but we do not include it here. -/
@[wikidata Q381892]
class CompactSpace : Prop where
  /-- In a compact space, `Set.univ` is a compact set. -/
  isCompact_univ : IsCompact (Set.univ : Set X)
```

#### WeaklyLocallyCompactSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L306-L313

Excerpt SHA256: `024b435a4309a82bf671bad68d52d289db4c21c27fa6bdcc01b5f83945df8ea2`

```lean

/-- We say that a topological space is a *weakly locally compact space*,
if each point of this space admits a compact neighborhood. -/
class WeaklyLocallyCompactSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- Every point of a weakly locally compact space admits a compact neighborhood. -/
  exists_compact_mem_nhds (x : X) : ∃ s, IsCompact s ∧ s ∈ 𝓝 x

export WeaklyLocallyCompactSpace (exists_compact_mem_nhds)
```

#### LocallyCompactSpace

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L315-L326

Excerpt SHA256: `6425a4e0c98ef2c5b36afbb98cfe9e99911497ea53fd9b3d9c55f71b654de65c`

```lean
/-- There are various definitions of "locally compact space" in the literature,
which agree for Hausdorff spaces but not in general.
This one is the precise condition on X needed
for the evaluation map `C(X, Y) × X → Y` to be continuous for all `Y`
when `C(X, Y)` is given the compact-open topology.

See also `WeaklyLocallyCompactSpace`, a typeclass that only assumes
that each point has a compact neighborhood. -/
class LocallyCompactSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a locally compact space,
  every neighbourhood of every point contains a compact neighbourhood of that same point. -/
  local_compact_nhds : ∀ (x : X), ∀ n ∈ 𝓝 x, ∃ s ∈ 𝓝 x, s ⊆ n ∧ IsCompact s
```

### Mathlib/Topology/Separation/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/Basic.lean

File SHA256: `96c74f410b14c3adecc1cb06d90d9d7a61bbb1529c18000426687bee99ba6991`

Git blob: `2d39660bfd78f367e80c7ee07b36871de306e3f2`

License: Apache-2.0. Retained upstream header:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
```

#### R1Space

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/Basic.lean#L934-L948

Excerpt SHA256: `8a0a3cd26634e3559042c5988069e5b31a87a2176fcc8307e2af28c3fc962fb8`

```lean
section R1Space

/-- A topological space is called a *preregular* (a.k.a. R₁) space,
if any two topologically distinguishable points have disjoint neighbourhoods. -/
@[mk_iff r1Space_iff_specializes_or_disjoint_nhds]
class R1Space (X : Type*) [TopologicalSpace X] : Prop where
  specializes_or_disjoint_nhds (x y : X) : Specializes x y ∨ Disjoint (𝓝 x) (𝓝 y)

export R1Space (specializes_or_disjoint_nhds)

variable [R1Space X] {x y : X}

instance (priority := 100) : R0Space X where
  specializes_symm.symm _ _ h := (specializes_or_disjoint_nhds _ _).resolve_right <| fun hd ↦
    h.not_disjoint hd.symm
```

#### r1Space_iff_inseparable_or_disjoint_nhds

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/Basic.lean#L959-L962

Excerpt SHA256: `e366876b98798de4a24f01f7803dfce104b5f20c6e86635dfbdaa3e47e92290a`

```lean
theorem r1Space_iff_inseparable_or_disjoint_nhds {X : Type*} [TopologicalSpace X] :
    R1Space X ↔ ∀ x y : X, Inseparable x y ∨ Disjoint (𝓝 x) (𝓝 y) :=
  ⟨fun _h x y ↦ (specializes_or_disjoint_nhds x y).imp_left Specializes.inseparable, fun h ↦
    ⟨fun x y ↦ (h x y).imp_left Inseparable.specializes⟩⟩
```

#### IsCompact.closure_subset_of_isOpen

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/Basic.lean#L1017-L1022

Excerpt SHA256: `1e9c59da9024afc5135a5238356a7a5c24200a53c792a47629d19ea67429c716`

```lean
/-- In an R₁ space, if a compact set `K` is contained in an open set `U`,
then its closure is also contained in `U`. -/
theorem IsCompact.closure_subset_of_isOpen {K : Set X} (hK : IsCompact K)
    {U : Set X} (hU : IsOpen U) (hKU : K ⊆ U) : closure K ⊆ U := by
  rw [hK.closure_eq_biUnion_inseparable, iUnion₂_subset_iff]
  exact fun x hx y hxy ↦ (hxy.mem_open_iff hU).1 (hKU hx)
```

#### IsCompact.closure

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/Basic.lean#L1024-L1028

Excerpt SHA256: `3673e6d87035839e33c63ff973ea55292945cfaeb4161e43069451e8de3a6510`

```lean
/-- The closure of a compact set in an R₁ space is a compact set. -/
protected theorem IsCompact.closure {K : Set X} (hK : IsCompact K) : IsCompact (closure K) := by
  refine isCompact_of_finite_subcover fun U hUo hKU ↦ ?_
  rcases hK.elim_finite_subcover U hUo (subset_closure.trans hKU) with ⟨t, ht⟩
  exact ⟨t, hK.closure_subset_of_isOpen (isOpen_biUnion fun _ _ ↦ hUo _) ht⟩
```

#### weak-local-R1-context

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/Basic.lean#L1177-L1184

Excerpt SHA256: `d537e2c5c6e2b468aee44826a6bdbd7f4e2bc8eea20dc008ed06a63ef0078f08`

```lean
/-!
### Lemmas about a weakly locally compact R₁ space

In fact, a space with these properties is locally compact and regular.
Some lemmas are formulated using the latter assumptions below.
-/

variable [WeaklyLocallyCompactSpace X]
```

#### weak-local-R1-upgrade

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/Basic.lean#L1197-L1200

Excerpt SHA256: `3e9a138512815e7f16b68792e363db518d071570500704f7a6c2bc73526239a3`

```lean
-- see Note [lower instance priority]
/-- A weakly locally compact R₁ space is locally compact. -/
instance (priority := 80) WeaklyLocallyCompactSpace.locallyCompactSpace : LocallyCompactSpace X :=
  .of_hasBasis isCompact_isClosed_basis_nhds fun _ _ ⟨_, h, _⟩ ↦ h
```

### Mathlib/Topology/GDelta/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean

File SHA256: `839130eb18758aa2bfcbe3ef40c98fcf9e0827458293fbdb5d04a5ec43b2d08a`

Git blob: `feae671419368d0d284d9ed57c536b6b54afba33`

License: Apache-2.0. Retained upstream header:

```lean
/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
```

#### IsGδ

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean#L62-L64

Excerpt SHA256: `7e136567a7e24bfece5698ef37f33eb8f5cefd4a7610ba8f35c4f9e765917187`

```lean
/-- A Gδ set is a countable intersection of open sets. -/
def IsGδ (s : Set X) : Prop :=
  ∃ T : Set (Set X), (∀ t ∈ T, IsOpen t) ∧ T.Countable ∧ s = ⋂₀ T
```

#### isGδ_iff_eq_iInter_nat

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

### Mathlib/Topology/Neighborhoods.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Neighborhoods.lean

File SHA256: `ef0e4d65986641366ffcc380a613f210207fee31e8640e1488a8cae41395383a`

Git blob: `8bfc6cc6c85396ab77a34b0725508d165b3903f4`

License: Apache-2.0. Retained upstream header:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

#### mem_nhds_iff

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Neighborhoods.lean#L64-L66

Excerpt SHA256: `3920d4125f26e7f74ea0eb050f41fa4c4f00ef056b57524cd6b93066efb1d515`

```lean
theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t :=
  (nhds_basis_opens x).mem_iff.trans <| exists_congr fun _ =>
    ⟨fun h => ⟨h.2, h.1.2, h.1.1⟩, fun h => ⟨⟨h.2.2, h.2.1⟩, h.1⟩⟩
```

### Mathlib/Topology/Inseparable.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Inseparable.lean

File SHA256: `dca5fb650652280da014c44e928d3992da800db80c65ffebcdf51e3f2e5c0556`

Git blob: `59b2ec991587de238c6e0c425547d933a2a33a35`

License: Apache-2.0. Retained upstream header:

```lean
/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yury Kudryashov
-/
```

#### inseparable_iff_forall_isOpen

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Inseparable.lean#L468-L470

Excerpt SHA256: `f8a7fe770ae6e0b6d8a20e3e969ea32f7882c63108a2caa5e305ae36cbdebb6e`

```lean
theorem inseparable_iff_forall_isOpen : (x ~ᵢ y) ↔ ∀ s : Set X, IsOpen s → (x ∈ s ↔ y ∈ s) := by
  simp only [inseparable_iff_specializes_and, specializes_iff_forall_open, ← forall_and, ← iff_def,
    Iff.comm]
```

### Mathlib/Topology/Constructions/SumProd.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions/SumProd.lean

File SHA256: `35d6365bebe8c5d331fe01289e857ccc81e6f6392b1f01835d834a35a6931666`

Git blob: `ff2a20dc397df5309720b3f7c1fdbe83244dfbfc`

License: Apache-2.0. Retained upstream header:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
```

#### product-topology

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Constructions/SumProd.lean#L50-L56

Excerpt SHA256: `bf3f7010718cef54196c57b689842a501f33f5fb0d2c152012fd10e8c5fc1f14`

```lean
    TopologicalSpace (X ⊕ Y) :=
  coinduced Sum.inl t₁ ⊔ coinduced Sum.inr t₂

instance instTopologicalSpaceProd [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y] :
    TopologicalSpace (X × Y) :=
  induced Prod.fst t₁ ⊓ induced Prod.snd t₂

```

### Mathlib/Topology/Closure.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Closure.lean

File SHA256: `d4e49fd0b092d34d5db79261bfc58b69ad3383a113ff2a0f54c0912a8b9afb5c`

Git blob: `557a4cd1768bc437e6f55fd9635ad07eba7c6080`

License: Apache-2.0. Retained upstream header:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

#### dense_iff_inter_open

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Closure.lean#L407-L416

Excerpt SHA256: `9a409a04b115c02363949db371f217b2c698b697dc6265202576be7c5de7920f`

```lean
/-- A set is dense if and only if it has a nonempty intersection with each nonempty open set. -/
theorem dense_iff_inter_open :
    Dense s ↔ ∀ U, IsOpen U → U.Nonempty → (U ∩ s).Nonempty := by
  constructor <;> intro h
  · rintro U U_op ⟨x, x_in⟩
    exact mem_closure_iff.1 (h _) U U_op x_in
  · intro x
    rw [mem_closure_iff]
    intro U U_op x_in
    exact h U U_op ⟨_, x_in⟩
```

### Mathlib/Topology/Compactness/LocallyCompact.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/LocallyCompact.lean

File SHA256: `4b6595bb61a6c53eee398a96f7fb2301cf24f400f82ce9fdfe4ee1d5dd3e64ce`

Git blob: `a8daae99ac29b2ad06fbe9308dc7fb988c732763`

License: Apache-2.0. Retained upstream header:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
```

#### compact-to-weak-local

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/LocallyCompact.lean#L36-L37

Excerpt SHA256: `337424b6e8af5ae2df1fba0f833fd930023be8f7028cd4cb78c2aad2d7d12169`

```lean
instance (priority := 100) [CompactSpace X] : WeaklyLocallyCompactSpace X where
  exists_compact_mem_nhds _ := ⟨univ, isCompact_univ, univ_mem⟩
```

### Mathlib/Topology/Compactness/Compact.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Compact.lean

File SHA256: `3fc7ffe7db4db0a2de07d6fdf0e65da486b3dced1f3bac4d58ab869a92f4ac64`

Git blob: `30fc9322f4ce78f847a592b0035bf5edfc65f33c`

License: Apache-2.0. Retained upstream header:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
```

#### closed-nested-intersection

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Compact.lean#L336-L345

Excerpt SHA256: `b269cbf03f8700525fb6302bd5a19b8a6fd83bface21df1286d79a3e3b0db4ee`

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

#### isCompact_iff_finite_subcover

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Compact.lean#L384-L390

Excerpt SHA256: `758302c18c0095b5390d3d24055fba6ef1b52b1356027614c3370500aeb0de37`

```lean
/-- A set `s` is compact if and only if
for every open cover of `s`, there exists a finite subcover. -/
theorem isCompact_iff_finite_subcover :
    IsCompact s ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) → ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  ⟨fun hs => hs.elim_finite_subcover, isCompact_of_finite_subcover⟩

```

### Mathlib/Topology/Sets/Compacts.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Sets/Compacts.lean

File SHA256: `9f897430e92d1bb496298d6c4daefecb76232f79c4e9cdee7d137eecaf77b5fc`

Git blob: `76e5a262cb3b16845ecc95c68b8955b4cd24526d`

License: Apache-2.0. Retained upstream header:

```lean
/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
```

#### Compacts

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Sets/Compacts.lean#L33-L57

Excerpt SHA256: `7cd74f9ed016c88488c233b5f236947d98e41e4fd8d3d5857a5225197405d707`

```lean
namespace TopologicalSpace

/-! ### Compact sets -/

/-- The type of compact sets of a topological space. -/
structure Compacts (α : Type*) [TopologicalSpace α] where
  /-- the carrier set, i.e. the points in this set -/
  carrier : Set α
  isCompact' : IsCompact carrier

namespace Compacts

instance : SetLike (Compacts α) α where
  coe := Compacts.carrier
  coe_injective s t h := by cases s; cases t; congr

instance : PartialOrder (Compacts α) := .ofSetLike (Compacts α) α

/-- See Note [custom simps projection]. -/
def Simps.coe (s : Compacts α) : Set α := s

initialize_simps_projections Compacts (carrier → coe, as_prefix coe)

protected theorem isCompact (s : Compacts α) : IsCompact (s : Set α) :=
  s.isCompact'
```

#### PositiveCompacts

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Sets/Compacts.lean#L645-L674

Excerpt SHA256: `35d189bfffebda7a853da2e7a64458f1ad022cac40c953872c3818a4fc2dacd1`

```lean

/-- The type of compact sets with nonempty interior of a topological space.
See also `TopologicalSpace.Compacts` and `TopologicalSpace.NonemptyCompacts`. -/
structure PositiveCompacts (α : Type*) [TopologicalSpace α] extends Compacts α where
  interior_nonempty' : (interior carrier).Nonempty

namespace PositiveCompacts

instance : SetLike (PositiveCompacts α) α where
  coe s := s.carrier
  coe_injective s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

instance : PartialOrder (PositiveCompacts α) := .ofSetLike (PositiveCompacts α) α

/-- See Note [custom simps projection]. -/
def Simps.coe (s : PositiveCompacts α) : Set α := s

initialize_simps_projections PositiveCompacts (carrier → coe, as_prefix coe, as_prefix toCompacts)

protected theorem isCompact (s : PositiveCompacts α) : IsCompact (s : Set α) :=
  s.isCompact'

theorem interior_nonempty (s : PositiveCompacts α) : (interior (s : Set α)).Nonempty :=
  s.interior_nonempty'

protected theorem nonempty (s : PositiveCompacts α) : (s : Set α).Nonempty :=
  s.interior_nonempty.mono interior_subset
```

#### positive-compact-closure-shrinking

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Sets/Compacts.lean#L744-L747

Excerpt SHA256: `60faf91ff0c2deb86b5248d9eca69b99b9996fccb1b1051e6ee07d83f2dcffad`

```lean
theorem _root_.IsOpen.exists_positiveCompacts_closure_subset [R1Space α] [LocallyCompactSpace α]
    {U : Set α} (ho : IsOpen U) (hn : U.Nonempty) : ∃ K : PositiveCompacts α, closure ↑K ⊆ U :=
  let ⟨K, hKU⟩ := exists_positiveCompacts_subset ho hn
  ⟨K, K.isCompact.closure_subset_of_isOpen ho hKU⟩
```

### Mathlib/Data/Set/Pairwise/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Pairwise/Basic.lean

File SHA256: `49a08e66f604f22b7978292a7569496c1c69b6e16014aee317ebf9f9750fa6d6`

Git blob: `fa5e633790a26b7451827cbd834d87dafe1f4f10`

License: Apache-2.0. Retained upstream header:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

#### PairwiseDisjoint

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Pairwise/Basic.lean#L250-L258

Excerpt SHA256: `4d382da5fe077b9a61f80db6db72f9596cf47ba580a857100189218aa52ae285`

```lean

/-- A set is `PairwiseDisjoint` under `f`, if the images of any distinct two elements under `f`
are disjoint.

`s.Pairwise Disjoint` is (definitionally) the same as `s.PairwiseDisjoint id`. We prefer the latter
in order to allow dot notation on `Set.PairwiseDisjoint`, even though the former unfolds more
nicely. -/
def PairwiseDisjoint (s : Set ι) (f : ι → α) : Prop :=
  s.Pairwise (Disjoint on f)
```

### Mathlib/Logic/Pairwise.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Pairwise.lean

File SHA256: `ccac95d1101a308ae38946e81caaa6d2c32e7e90ed99f7305dba9f01a955e62f`

Git blob: `7a2f0dc7819c5656049e1d99f6ba0be56f1e04ca`

License: Apache-2.0. Retained upstream header:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

#### Set.Pairwise

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Pairwise.lean#L80-L84

Excerpt SHA256: `dc07f59c0a776d37ad78e1161dd9c87ae848c879ee2bdabe152d0a979ac4affa`

```lean
namespace Set

/-- The relation `r` holds pairwise on the set `s` if `r x y` for all *distinct* `x y ∈ s`. -/
protected def Pairwise (s : Set α) (r : α → α → Prop) :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → r x y
```

### Mathlib/Order/Disjoint.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Disjoint.lean

File SHA256: `5c59598e126b8345a9373277f8e30c0d52b3fce1080a96281f1dc54bc6dd619c`

Git blob: `7d5339050bb81a9d325ca7536bbe37dba409813f`

License: Apache-2.0. Retained upstream header:

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

#### Disjoint

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Disjoint.lean#L29-L49

Excerpt SHA256: `343e7f81bb0f165ed1d47af17cc8027a7a26b634ca77239d069eb87f9f7e178b`

```lean
variable {α : Type*}

section Disjoint

section PartialOrderBot

variable [PartialOrder α] [OrderBot α] {a b c d : α}

/-- Two elements of a lattice are disjoint if their inf is the bottom element.
  (This generalizes disjoint sets, viewed as members of the subset lattice.)

Note that we define this without reference to `⊓`, as this allows us to talk about orders where
the infimum is not unique, or where implementing `Inf` would require additional `Decidable`
arguments. -/
@[to_dual /-- Two elements of a lattice are codisjoint if their sup is the top element.

Note that we define this without reference to `⊔`, as this allows us to talk about orders where
the supremum is not unique, or where implementing `Sup` would require additional `Decidable`
arguments. -/]
def Disjoint (a b : α) : Prop :=
  ∀ ⦃x⦄, x ≤ a → x ≤ b → x ≤ ⊥
```

### Mathlib/Data/Set/Disjoint.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Disjoint.lean

File SHA256: `21e4643bfcae089dbbca262cb9d4b4bad1ad1cd77adf31ae43f4d2f2ab69e492`

Git blob: `e454989683e886f35bb9d6ef45c429eaadbd0f2d`

License: Apache-2.0. Retained upstream header:

```lean
/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
```

#### set-disjoint

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Disjoint.lean#L29-L40

Excerpt SHA256: `16a8ba9d0314facecc723d1659f71529b6cad3dcdb4c213134528acae5f363ab`

```lean
protected theorem disjoint_iff : Disjoint s t ↔ s ∩ t ⊆ ∅ :=
  disjoint_iff_inf_le

theorem disjoint_iff_inter_eq_empty : Disjoint s t ↔ s ∩ t = ∅ :=
  disjoint_iff

theorem _root_.Disjoint.inter_eq : Disjoint s t → s ∩ t = ∅ :=
  Disjoint.eq_bot

@[grind =]
theorem disjoint_left : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t :=
  disjoint_iff_inf_le.trans <| forall_congr' fun _ => not_and
```
