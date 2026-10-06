# Definition fidelity

The type `X` is the continuum, with its own topology. `IsSubcontinuum K` means
`IsCompact K ∧ IsConnected K`, so a subcontinuum is nonempty. The literal
`composant x` is the union of proper subcontinua containing `x`. No point is
adjoined to it. In a singleton space it is empty. Point membership, density,
connectedness, the cover, and uncountability use `Nontrivial X`.

Indecomposability is needed for equal-or-disjoint composants and meagreness.
The countable representation uses second countability, compactness and
Hausdorffness, without indecomposability or nondegeneracy. Meagreness is a
countable union condition, not nowhere density of the composant itself.

For a continuum inside a larger space, use its subtype with the induced
topology. All densities and connectedness statements are relative to that
continuum. The complete project definition bodies occur in both Challenge
and Solution and are compared as raw Lean expressions and universe lists.

The bounded source dossier preserves complete original files, attribution,
licenses, immutable source identities and full indexed declaration bodies.
The `.lean.txt` copies are source evidence and are not imported modules.

## TopologicalSpace

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean) (lines 73 to 83).

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

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean) (lines 95 to 95).

```lean
def IsOpen : Set X → Prop := TopologicalSpace.IsOpen
```

## IsClosed

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean) (lines 107 to 109).

```lean
class IsClosed (s : Set X) : Prop where
  /-- The complement of a closed set is an open set. -/
  isOpen_compl : IsOpen sᶜ
```

## IsPreconnected

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Connected/Basic.lean) (lines 50 to 52).

```lean
def IsPreconnected (s : Set α) : Prop :=
  ∀ u v : Set α, IsOpen u → IsOpen v → s ⊆ u ∪ v → (s ∩ u).Nonempty → (s ∩ v).Nonempty →
    (s ∩ (u ∩ v)).Nonempty
```

## IsConnected

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Connected/Basic.lean) (lines 55 to 56).

```lean
def IsConnected (s : Set α) : Prop :=
  s.Nonempty ∧ IsPreconnected s
```

## PreconnectedSpace

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Connected/Basic.lean) (lines 697 to 699).

```lean
class PreconnectedSpace (α : Type u) [TopologicalSpace α] : Prop where
  /-- The universal set `Set.univ` in a preconnected space is a preconnected set. -/
  isPreconnected_univ : IsPreconnected (univ : Set α)
```

## ConnectedSpace

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Connected/Basic.lean) (lines 705 to 707).

```lean
class ConnectedSpace (α : Type u) [TopologicalSpace α] : Prop extends PreconnectedSpace α where
  /-- A connected space is nonempty. -/
  toNonempty : Nonempty α
```

## CompactSpace

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean) (lines 297 to 299).

```lean
class CompactSpace : Prop where
  /-- In a compact space, `Set.univ` is a compact set. -/
  isCompact_univ : IsCompact (Set.univ : Set X)
```

## IsCompact

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Filter.lean) (lines 290 to 291).

```lean
def IsCompact (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f
```

## isCompact_iff_finite_subcover

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Compactness/Compact.lean) (lines 386 to 389).

```lean
theorem isCompact_iff_finite_subcover :
    IsCompact s ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) → ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  ⟨fun hs => hs.elim_finite_subcover, isCompact_of_finite_subcover⟩
```

## T2Space

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Separation/Hausdorff.lean) (lines 85 to 87).

```lean
class T2Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Every two points in a Hausdorff space admit disjoint open neighbourhoods. -/
  t2 : Pairwise fun x y => ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v
```

## interior

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean) (lines 122 to 123).

```lean
def interior (s : Set X) : Set X :=
  ⋃₀ { t | IsOpen t ∧ t ⊆ s }
```

## closure

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean) (lines 126 to 127).

```lean
def closure (s : Set X) : Set X :=
  ⋂₀ { t | IsClosed t ∧ s ⊆ t }
```

## IsNowhereDense

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean) (lines 200 to 200).

```lean
def IsNowhereDense (s : Set X) := interior (closure s) = ∅
```

## Nontrivial

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Nontrivial/Defs.lean) (lines 28 to 30).

```lean
class Nontrivial (α : Type*) : Prop where
  /-- In a nontrivial type, there exists a pair of distinct terms. -/
  exists_pair_ne : ∃ x y : α, x ≠ y
```

## subtype topology

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean) (lines 76 to 78).

```lean
instance _root_.instTopologicalSpaceSubtype {p : X → Prop} [t : TopologicalSpace X] :
    TopologicalSpace (Subtype p) :=
  induced (↑) t
```

## TopologicalSpace.induced

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Induced.lean) (lines 64 to 74).

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

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean) (lines 146 to 147).

```lean
def Dense (s : Set X) : Prop :=
  ∀ x, x ∈ closure s
```

## BaireSpace

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Defs/Basic.lean) (lines 239 to 240).

```lean
class BaireSpace (X : Type*) [TopologicalSpace X] : Prop where
  baire_property : ∀ f : ℕ → Set X, (∀ n, IsOpen (f n)) → (∀ n, Dense (f n)) → Dense (⋂ n, f n)
```

## SecondCountableTopology

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean) (lines 793 to 795).

```lean
class _root_.SecondCountableTopology : Prop where
  /-- There exists a countable set of sets that generates the topology. -/
  is_open_generated_countable : ∃ b : Set (Set α), b.Countable ∧ t = TopologicalSpace.generateFrom b
```

## IsTopologicalBasis

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean) (lines 73 to 79).

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

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Bases.lean) (lines 826 to 827).

```lean
def countableBasis [SecondCountableTopology α] : Set (Set α) :=
  (exists_countable_basis α).choose
```

## connectedComponent

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Connected/Basic.lean) (lines 495 to 496).

```lean
def connectedComponent (x : α) : Set α :=
  ⋃₀ { s : Set α | IsPreconnected s ∧ x ∈ s }
```

## connectedComponentIn

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/Connected/Basic.lean) (lines 505 to 506).

```lean
noncomputable def connectedComponentIn (F : Set α) (x : α) : Set α :=
  if h : x ∈ F then (↑) '' connectedComponent (⟨x, h⟩ : F) else ∅
```

## IsMeagre

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean) (lines 284 to 284).

```lean
def IsMeagre (s : Set X) := sᶜ ∈ residual X
```

## residual

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/GDelta/Basic.lean) (lines 170 to 171).

```lean
def residual (X : Type*) [TopologicalSpace X] : Filter X :=
  Filter.countableGenerate { t | IsOpen t ∧ Dense t }
```

## Filter.countableGenerate

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/CountableInter.lean) (lines 281 to 283).

```lean
def countableGenerate : Filter α :=
  ofCountableInter {s | CountableGenerateSets g s} (fun _ ↦ .sInter) fun _ _ ↦ .superset
deriving CountableInterFilter
```

## Filter.CountableGenerateSets

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Filter/CountableInter.lean) (lines 272 to 277).

```lean
inductive CountableGenerateSets : Set α → Prop
  | basic {s : Set α} : s ∈ g → CountableGenerateSets s
  | univ : CountableGenerateSets univ
  | superset {s t : Set α} : CountableGenerateSets s → s ⊆ t → CountableGenerateSets t
  | sInter {S : Set (Set α)} :
    S.Countable → (∀ s ∈ S, CountableGenerateSets s) → CountableGenerateSets (⋂₀ S)
```

## Countable

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Basic/Countable/Defs.lean) (lines 41 to 43).

```lean
class Countable (α : Sort u) : Prop where
  /-- A type `α` is countable if there exists an injective map `α → ℕ`. -/
  exists_injective_nat' : ∃ f : α → ℕ, Injective f
```

## Set.Countable

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Countable.lean) (lines 49 to 49).

```lean
protected def Countable (s : Set α) : Prop := Countable s
```

## Set.range

[Complete pinned source](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Set/Operations.lean) (lines 173 to 173).

```lean
def range (f : ι → α) : Set α := {x | ∃ y, f y = x}
```

