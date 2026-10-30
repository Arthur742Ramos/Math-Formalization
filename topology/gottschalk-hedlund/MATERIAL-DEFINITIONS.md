# Material imported definitions: provisional source inventory

Pinned excerpts and semantic bridges require independent completeness and mathematical fidelity review; exact compilation evidence is recorded separately. The exact interpretations of real numbers, absolute value, subtraction, finite summation and product topology still require expansion and independent review. Lean core provenance is supplemental and is not authenticated by the Mathlib-only checker.
- `TopologicalSpace`: A topology supplies open sets on X and the relevant product spaces. Used by: `GottschalkHedlund.bounded_sums_iff_transfer`, `GottschalkHedlund.transfer_difference_constant`, `GottschalkHedlund.bounded_sums_skew_conjugacy`.
- `IsOpen`: The open-set predicate supplied by the topology. Used by: `GottschalkHedlund.bounded_sums_iff_transfer`, `GottschalkHedlund.transfer_difference_constant`, `GottschalkHedlund.bounded_sums_skew_conjugacy`.
- `closure`: The topological closure of a set. Used by: `GottschalkHedlund.bounded_sums_iff_transfer`, `GottschalkHedlund.transfer_difference_constant`, `GottschalkHedlund.bounded_sums_skew_conjugacy`.
- `Continuous`: Preimages of open sets are open; applies to T, g and transfer functions. Used by: `GottschalkHedlund.bounded_sums_iff_transfer`, `GottschalkHedlund.transfer_difference_constant`, `GottschalkHedlund.bounded_sums_skew_conjugacy`.
- `Filter`: Filter structures underlie compactness and topology definitions. Used by: `GottschalkHedlund.bounded_sums_iff_transfer`, `GottschalkHedlund.transfer_difference_constant`, `GottschalkHedlund.bounded_sums_skew_conjugacy`.
- `IsCompact`: Compactness in the ambient topology, used in the compact-space assumption. Used by: `GottschalkHedlund.bounded_sums_iff_transfer`, `GottschalkHedlund.bounded_sums_skew_conjugacy`.
- `CompactSpace`: The whole underlying space is compact. Used by: `GottschalkHedlund.bounded_sums_iff_transfer`, `GottschalkHedlund.bounded_sums_skew_conjugacy`.
- `Dense`: The closure of the set is the entire space. Used by: `GottschalkHedlund.bounded_sums_iff_transfer`, `GottschalkHedlund.transfer_difference_constant`, `GottschalkHedlund.bounded_sums_skew_conjugacy`.
- `Set.range`: The set of values attained by a function. Used by: `GottschalkHedlund.bounded_sums_iff_transfer`, `GottschalkHedlund.transfer_difference_constant`, `GottschalkHedlund.bounded_sums_skew_conjugacy`.
- `Finset`: A finite duplicate-free index set; Birkhoff sums use range n. Used by: `GottschalkHedlund.bounded_sums_iff_transfer`, `GottschalkHedlund.bounded_sums_skew_conjugacy`.
- `Nat.iterate`: Forward natural iteration has the identity at zero; no inverse iterates are assumed. Used by: `GottschalkHedlund.bounded_sums_iff_transfer`, `GottschalkHedlund.transfer_difference_constant`, `GottschalkHedlund.bounded_sums_skew_conjugacy`.
- `T2Space`: Distinct points admit disjoint open neighborhoods. Used by: `GottschalkHedlund.bounded_sums_iff_transfer`, `GottschalkHedlund.bounded_sums_skew_conjugacy`.
- `Homeomorph`: A bijection with continuous forward and inverse functions; the selected result uses it for H, not T. Used by: `GottschalkHedlund.bounded_sums_skew_conjugacy`.
- `Equiv`: A function with a two-sided inverse; Homeomorph extends this structure. Used by: `GottschalkHedlund.bounded_sums_skew_conjugacy`.
- `DenseRange`: The range of the indicated forward orbit map is dense. Used by: `GottschalkHedlund.bounded_sums_iff_transfer`, `GottschalkHedlund.transfer_difference_constant`, `GottschalkHedlund.bounded_sums_skew_conjugacy`.
- `birkhoffSum`: The finite sum of g along the first n forward iterates; the n=0 sum is zero. Used by: `GottschalkHedlund.bounded_sums_iff_transfer`, `GottschalkHedlund.bounded_sums_skew_conjugacy`.

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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L150-L150
```lean
def DenseRange {α : Type*} (f : α → X) := Dense (range f)
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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Dynamics/BirkhoffSum/Basic.lean
SHA256 `437b84619d9ab6b388c0877c7059c0f64ece9b24265c1f38cde2532950bedf93`

```lean
/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
```

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Dynamics/BirkhoffSum/Basic.lean#L30-L31
```lean
/-- The sum of values of `g` on the first `n` points of the orbit of `x` under `f`. -/
def birkhoffSum (f : α → α) (g : α → M) (n : ℕ) (x : α) : M := ∑ k ∈ range n, g (f^[k] x)
```

## Lean core supplement

https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Prelude.lean
SHA256 `cc9f337a5d8bd00768121701bceb0661ac63e01831a9aa34b282f37c689a6c39`, Git blob `f87ee970af5149d74434f09a89aedff1a8fdb2d2`.

`Nonempty` lines 839-841, SHA256 `409b9d791b14a599f13bb14741bdfbfc112bc04bd4fc41d9924083fa47df7598`:
```lean
class inductive Nonempty (α : Sort u) : Prop where
  /-- If `val : α`, then `α` is nonempty. -/
  | intro (val : α) : Nonempty α
```
