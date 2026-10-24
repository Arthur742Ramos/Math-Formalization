# Material imported definitions

Selected: Furstenberg.weakMixing_iff_product_transitive, Furstenberg.hitting_refinement, Furstenberg.finite_refinement, Furstenberg.finite_simultaneous_hitting, Furstenberg.finite_power_transitive.

- `TopologicalSpace`: The supplied topology on X and its actual binary/Pi product topology; no Baire, metric, separation or countability property is implicit.
- `IsOpen`: Open in the supplied topology; the refinement produces genuinely open W,Z by continuity of iterated preimages. Product opens are tested through actual rectangles or finite-coordinate boxes.
- `Continuous`: Inverse images of all opens are open for f. Iteration preserves continuity, ensuring each refined pair remains open; not a hidden bijectivity/surjectivity assumption.
- `TopologicalSpace.induced`: Inverse-image topology along each actual coordinate projection; binary product is the infimum of the two induced topologies and Pi product the infimum over coordinates.
- `Finset`: A duplicate-free finite multiset of constraint indices; the induction retains a nonempty open pair refining every previously accumulated hitting condition. Empty family is explicitly included.
- `Nat.iterate`: The zero iterate is identity; the successor iterate applies f once then the previous iterate. Time is a natural number including zero. Commutativity of powers follows from additive iteration laws, not from an invertibility premise.

Binary/Pi topologies, fixed maps, Hit and natural-iterate recursion have literal bridges. Weak mixing versus actual product transitivity is a proved equivalence. Core Nonempty and Fin are separately retained in CORE-DEFINITIONS.md at the compiler pin; no empty-family/zeroth-power omission.

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean
SHA256 `6a16294b9ce69e6f245f45abc59d45db011f2a1c545b4d5d403ccaca5b17c99c`

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L155-L158
```lean
structure Continuous (f : X → Y) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean#L76-L78
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

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean#L125-L131
```lean
open scoped Topology

/-- A set is called a neighborhood of `x` if it contains an open set around `x`. The set of all
neighborhoods of `x` forms a filter, the neighborhood filter at `x`, is here defined as the
infimum over the principal filters of all open sets containing `x`. -/
irreducible_def nhds (x : X) : Filter X :=
  ⨅ s ∈ { s : Set X | x ∈ s ∧ IsOpen s }, 𝓟 s
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
