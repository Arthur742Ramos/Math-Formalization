# Material imported meanings and game-model audit

This inventory is bound to Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55 and Lean v4.35.0-rc2. Both independently imported test modules compile these meanings. Literal unfolding, class-field projections and proved equivalences are distinguished. Source hashes alone do not establish semantic completeness or successful canonical checks.

The full model is in BanachMazur.lean and its byte-identical Challenge. OpenMove is the subtype of all nonempty open subsets; FirstStrategy has a total move function on full finite opponent histories and a response-inclusion field. A deterministic player's own preceding moves can be reconstructed from these histories, so no information is lost by storing opponent moves only. Histories are reverse chronological: at roundn they contain exactly a(n-1),…,a0, with lengthn. The exact List constructors and length are retained separately in CORE-DEFINITIONS.md. Follows imposes every second-player inclusion; FirstStrategy.responds imposes every first-player inclusion, including the next response. Equality is allowed. The two intersections are proved equal. FirstWins universally quantifies compatible infinite plays and requires empty intersection. The characterization is ∀strategy∃defeatingplay, not existence of a single second-player winning strategy or determinacy. Every actual strategy admits a compatible play; empty spaces have no initial move or strategy.

The used_by lists cover the selected declarations’ explicit material occurrences and their critical transitive proof dependencies; they are not restricted to direct calls. The principal argument uses disjoint strategy-response levels to choose a coherent branch through a Baire point. Indexed disjointness quantifies different histories even if response sets coincide. IsEmpty concerns type emptiness, while Set.Nonempty asserts existential membership. TopologicalSpace adds no separation or countability. BaireSpace is a class wrapper related to its field by constructor/projection proofs, not rfl. A future exact-source canonical result and rendering require their own immutable external receipts.

## BaireSpace

Every natural-number-indexed intersection of dense open sets is dense. No separation or nonempty hypothesis.

The class field uses Dense and IsOpen in the given arbitrary topology. Open-subspace Baireness supplies a point in the dense response levels.

Kind: class; bridge: class-fields. Both independent entrypoints compile the literal predicates or constructor/projection class equivalence and any stated proved characterization. Upstream infrastructure is credited; no new selected theorem or axiom is introduced.

Used by: BanachMazur.exists_commonPoint_play, BanachMazur.not_firstWins_of_baireSpace, BanachMazur.exists_firstWins_of_not_baireSpace, BanachMazur.baireSpace_iff_no_firstWins.

## Dense

Every ambient point belongs to the closure; equivalently every nonempty open set meets the set.

Closure is the intersection of all closed supersets. The open-intersection characterization is proved, not literal unfolding.

Kind: def; bridge: literal-unfolding. Both independent entrypoints compile the literal predicates or constructor/projection class equivalence and any stated proved characterization. Upstream infrastructure is credited; no new selected theorem or axiom is introduced.

Used by: BanachMazur.exists_commonPoint_play, BanachMazur.not_firstWins_of_baireSpace, BanachMazur.exists_firstWins_of_not_baireSpace, BanachMazur.baireSpace_iff_no_firstWins.

## Set.PairwiseDisjoint

For every pair of distinct labels in the chosen family, their image sets are disjoint.

Set.Pairwise quantifies distinct labels; Disjoint on sets means empty intersection. Equal inhabited image sets are not exempt. No countability or universe identification is added.

Kind: def; bridge: literal-unfolding. Both independent entrypoints compile the literal predicates or constructor/projection class equivalence and any stated proved characterization. Upstream infrastructure is credited; no new selected theorem or axiom is introduced.

Used by: BanachMazur.exists_commonPoint_play, BanachMazur.not_firstWins_of_baireSpace, BanachMazur.baireSpace_iff_no_firstWins.

## IsOpen

The open-set predicate supplied by the given ambient topological-space structure.

IsOpen literally projects the chosen ambient topology. The space has no separation or countability requirement; both players choose all nonempty opens.

Kind: def; bridge: literal-unfolding. Both independent entrypoints compile the literal predicates or constructor/projection class equivalence and any stated proved characterization. Upstream infrastructure is credited; no new selected theorem or axiom is introduced.

Used by: BanachMazur.exists_compatiblePlay, BanachMazur.follows_intersection_eq, BanachMazur.exists_commonPoint_play, BanachMazur.not_firstWins_of_baireSpace, BanachMazur.exists_firstWins_of_not_baireSpace, BanachMazur.baireSpace_iff_no_firstWins, BanachMazur.isEmpty_firstStrategy.

## closure

The smallest closed superset: the intersection of every closed set containing the given set.

This term appears in the dense-refinement conclusion G subset closure of the union. IsClosed is the open-complement class; closure is not a compactness or Hausdorff assumption.

Kind: def; bridge: literal-unfolding. Both independent entrypoints compile the literal predicates or constructor/projection class equivalence and any stated proved characterization. Upstream infrastructure is credited; no new selected theorem or axiom is introduced.

Used by: BanachMazur.exists_commonPoint_play, BanachMazur.not_firstWins_of_baireSpace, BanachMazur.exists_firstWins_of_not_baireSpace, BanachMazur.baireSpace_iff_no_firstWins.

## Set.Nonempty

There exists one element belonging to the set. A common point belongs to every move; one different point per round is insufficient.

Protected Set.Nonempty is an existential membership predicate. Intersections are literal universal membership; indexed Nonempty is not a compactness assumption.

Kind: def; bridge: literal-unfolding. Literal existential and common-point equivalence compile independently through both entrypoints.

Used by: BanachMazur.exists_compatiblePlay, BanachMazur.follows_intersection_eq, BanachMazur.exists_commonPoint_play, BanachMazur.not_firstWins_of_baireSpace, BanachMazur.exists_firstWins_of_not_baireSpace, BanachMazur.baireSpace_iff_no_firstWins, BanachMazur.isEmpty_firstStrategy.

## IsEmpty

The type has no elements: every element implies False.

Class field IsEmpty.false : X → False. This type-emptiness is distinct from set Nonempty; an empty space has no strategy because its initial open cannot be chosen.

Kind: class; bridge: class-fields. Constructor/projection equivalence compiled; not claimed to be definitional equality of class and field.

Used by: BanachMazur.isEmpty_firstStrategy.

## TopologicalSpace

An open-set predicate containing the whole space and closed under binary intersections and arbitrary unions.

The class is data carrying the open predicate and proofs of its axioms. It supplies no Hausdorff, regularity, metric, countability or nonempty condition.

Kind: class; bridge: class-fields. The exact class-field axioms compile through projections in both entrypoints; the data class is not falsely identified with a proposition.

Used by: BanachMazur.exists_compatiblePlay, BanachMazur.follows_intersection_eq, BanachMazur.exists_commonPoint_play, BanachMazur.not_firstWins_of_baireSpace, BanachMazur.exists_firstWins_of_not_baireSpace, BanachMazur.baireSpace_iff_no_firstWins, BanachMazur.isEmpty_firstStrategy.

## Pinned source Mathlib/Topology/Defs/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean

SHA256 6a16294b9ce69e6f245f45abc59d45db011f2a1c545b4d5d403ccaca5b17c99c; Git blob 326105821a5a8ce5041ccf8dce22779bd55fa923; Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

topology-open-closed: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L75-L110

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

interior-closure: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L117-L127

Excerpt SHA256 e08a72b7730b15a59ad60cdbfd00f72b089e1f72279df1dfb1ef9ed8736d0f07

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

Dense: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L145-L147

Excerpt SHA256 2a52522d35b48a1b96df7fa73b15254b113108436e633e0e45e5bdffc455fbf8

```lean
/-- A set is dense in a topological space if every point belongs to its closure. -/
def Dense (s : Set X) : Prop :=
  ∀ x, x ∈ closure s
```

BaireSpace: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L235-L240

Excerpt SHA256 977d5c7b2d9473e369aa9c2df40a2da2bea81bf7fb22f4978096b547f603e335

```lean
/-- The property `BaireSpace α` means that the topological space `α` has the Baire property:
any countable intersection of open dense subsets is dense.
Formulated here when the source space is ℕ.
Use `dense_iInter_of_isOpen` which works for any countable index type instead. -/
class BaireSpace (X : Type*) [TopologicalSpace X] : Prop where
  baire_property : ∀ f : ℕ → Set X, (∀ n, IsOpen (f n)) → (∀ n, Dense (f n)) → Dense (⋂ n, f n)
```

TopologicalSpace: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean#L71-L87

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

## Pinned source Mathlib/Topology/Closure.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Closure.lean

SHA256 d4e49fd0b092d34d5db79261bfc58b69ad3383a113ff2a0f54c0912a8b9afb5c; Git blob 557a4cd1768bc437e6f55fd9635ad07eba7c6080; Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
```

dense_iff_inter_open: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Closure.lean#L407-L416

Excerpt SHA256 9a409a04b115c02363949db371f217b2c698b697dc6265202576be7c5de7920f

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

## Pinned source Mathlib/Data/Set/Pairwise/Basic.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Pairwise/Basic.lean

SHA256 49a08e66f604f22b7978292a7569496c1c69b6e16014aee317ebf9f9750fa6d6; Git blob fa5e633790a26b7451827cbd834d87dafe1f4f10; Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

PairwiseDisjoint: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Pairwise/Basic.lean#L250-L258

Excerpt SHA256 4d382da5fe077b9a61f80db6db72f9596cf47ba580a857100189218aa52ae285

```lean

/-- A set is `PairwiseDisjoint` under `f`, if the images of any distinct two elements under `f`
are disjoint.

`s.Pairwise Disjoint` is (definitionally) the same as `s.PairwiseDisjoint id`. We prefer the latter
in order to allow dot notation on `Set.PairwiseDisjoint`, even though the former unfolds more
nicely. -/
def PairwiseDisjoint (s : Set ι) (f : ι → α) : Prop :=
  s.Pairwise (Disjoint on f)
```

## Pinned source Mathlib/Logic/Pairwise.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Pairwise.lean

SHA256 ccac95d1101a308ae38946e81caaa6d2c32e7e90ed99f7305dba9f01a955e62f; Git blob 7a2f0dc7819c5656049e1d99f6ba0be56f1e04ca; Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

Set.Pairwise: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Pairwise.lean#L80-L84

Excerpt SHA256 dc07f59c0a776d37ad78e1161dd9c87ae848c879ee2bdabe152d0a979ac4affa

```lean
namespace Set

/-- The relation `r` holds pairwise on the set `s` if `r x y` for all *distinct* `x y ∈ s`. -/
protected def Pairwise (s : Set α) (r : α → α → Prop) :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → r x y
```

## Pinned source Mathlib/Order/Disjoint.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Disjoint.lean

SHA256 5c59598e126b8345a9373277f8e30c0d52b3fce1080a96281f1dc54bc6dd619c; Git blob 7d5339050bb81a9d325ca7536bbe37dba409813f; Apache-2.0.

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
```

Disjoint: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Disjoint.lean#L29-L49

Excerpt SHA256 343e7f81bb0f165ed1d47af17cc8027a7a26b634ca77239d069eb87f9f7e178b

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

## Pinned source Mathlib/Data/Set/Disjoint.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Disjoint.lean

SHA256 21e4643bfcae089dbbca262cb9d4b4bad1ad1cd77adf31ae43f4d2f2ab69e492; Git blob e454989683e886f35bb9d6ef45c429eaadbd0f2d; Apache-2.0.

```lean
/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
```

set-disjoint: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Disjoint.lean#L29-L40

Excerpt SHA256 16a8ba9d0314facecc723d1659f71529b6cad3dcdb4c213134528acae5f363ab

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

## Pinned source Mathlib/Data/Set/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean

SHA256 4b5433ba90d229d2875756f2c486de41e2e1b5be89b7255be5fe7ed2e0c524c7; Git blob 866ef6ab673f737a4ffbb7b2138402d5c76e6c05; Apache-2.0.

```lean
/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
```

Set.Nonempty: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Defs.lean#L277-L281

Excerpt SHA256 cb3870fa0008d18792a7122276c41e3e45998a2f2defae575b4225f0a2cf53de

```lean
/-- The property `s.Nonempty` expresses the fact that the set `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def Nonempty (s : Set α) : Prop :=
  ∃ x, x ∈ s
```

## Pinned source Mathlib/Basic/IsEmpty/Defs.lean

https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/IsEmpty/Defs.lean

SHA256 4cc13389d971b07836334b2c9b2a1d979fa1f0043ea9e37a5ba08a9214765399; Git blob 8cddc87f06c29a7e02b57c48e725d0725febde92; Apache-2.0.

```lean
/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
```

IsEmpty: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/IsEmpty/Defs.lean#L26-L28

Excerpt SHA256 91cda3d147caf0690894eb7e775e12d73d277418a3818042a138e40d5cf7579e

```lean
/-- `IsEmpty α` expresses that `α` is empty. -/
class IsEmpty (α : Sort u) : Prop where
  protected false : α → False
```
