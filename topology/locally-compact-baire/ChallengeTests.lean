module
public import LCBChallenge

open LocallyCompactBaire Set TopologicalSpace

#check LocallyCompactBaire.exists_maximal_pairwiseDisjoint_refinement
#check LocallyCompactBaire.exists_pairwiseDisjoint_dense_refinement
#check LocallyCompactBaire.exists_dense_isGdelta_fiber_witness
#check LocallyCompactBaire.exists_dense_isGdelta_subset_image_fst
#check LocallyCompactBaire.baireSpace_prod
#check LocallyCompactBaire.baireSpace_prod_of_compact

-- All three type universes are independent, with arbitrary labels and no separation.
example {X : Type u} {A : Type v} (f : A → Set X) (P : A → Prop) :
    ∃ F : Set A, (∀ a ∈ F, P a) ∧ F.PairwiseDisjoint f ∧
      ∀ F' : Set A, (∀ a ∈ F', P a) → F'.PairwiseDisjoint f → F ⊆ F' → F' ⊆ F :=
  exists_maximal_pairwiseDisjoint_refinement f P

example {X : Type u} {A : Type v} [TopologicalSpace X]
    (f : A → Set X) (P : A → Prop) {G : Set X} (hG : IsOpen G)
    (hP : ∀ a, P a → IsOpen (f a) ∧ (f a).Nonempty ∧ f a ⊆ G)
    (hr : ∀ W : Set X, IsOpen W → W.Nonempty → W ⊆ G → ∃ a, P a ∧ f a ⊆ W) :
    ∃ F : Set A, (∀ a ∈ F, P a) ∧ F.PairwiseDisjoint f ∧
      (⋃ a ∈ F, f a) ⊆ G ∧ G ⊆ closure (⋃ a ∈ F, f a) :=
  exists_pairwiseDisjoint_dense_refinement f P hG hP hr

example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [BaireSpace X] [R1Space Y] [LocallyCompactSpace Y]
    (D : ℕ → Set (X × Y)) (ho : ∀ n, IsOpen (D n)) (hd : ∀ n, Dense (D n))
    {V : Set Y} (hVo : IsOpen V) (hVn : V.Nonempty) :
    ∃ G : Set X, IsGδ G ∧ Dense G ∧ ∀ x ∈ G, ∃ y ∈ V, ∀ n, (x, y) ∈ D n :=
  exists_dense_isGdelta_fiber_witness D ho hd hVo hVn

example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [BaireSpace X] [R1Space Y] [LocallyCompactSpace Y]
    {D : Set (X × Y)} (hg : IsGδ D) (hd : Dense D)
    {V : Set Y} (ho : IsOpen V) (hn : V.Nonempty) :
    ∃ G : Set X, IsGδ G ∧ Dense G ∧ G ⊆ Prod.fst '' (D ∩ (univ ×ˢ V)) :=
  exists_dense_isGdelta_subset_image_fst hg hd ho hn

-- No Baire-space, regularity, countability or nonempty hypotheses on Y beyond the stated classes.
example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [BaireSpace X] [R1Space Y] [LocallyCompactSpace Y] : BaireSpace (X × Y) :=
  baireSpace_prod

example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [BaireSpace X] [R1Space Y] [CompactSpace Y] : BaireSpace (X × Y) :=
  baireSpace_prod_of_compact


-- BEGIN material-imported-definition audit
section MaterialImportedDefinitions

open Filter
open scoped Topology

variable {Z : Type u} [TopologicalSpace Z]

example (A : Set Z) : closure A = ⋂₀ {C : Set Z | IsClosed C ∧ A ⊆ C} := rfl

example (U : Set Z) : IsOpen U ↔ TopologicalSpace.IsOpen U := Iff.rfl

-- Class wrappers are related to their fields by constructor/projection proofs.
example : BaireSpace Z ↔ ∀ D : ℕ → Set Z,
    (∀ n, IsOpen (D n)) → (∀ n, Dense (D n)) → Dense (⋂ n, D n) :=
  ⟨fun h => h.baire_property, fun h => ⟨h⟩⟩

example : R1Space Z ↔ ∀ x y : Z,
    Specializes x y ∨ Disjoint (𝓝 x) (𝓝 y) :=
  ⟨fun h => h.specializes_or_disjoint_nhds, fun h => ⟨h⟩⟩

-- The symmetric, topologically-indistinguishable formulation is a theorem.
example : R1Space Z ↔ ∀ x y : Z,
    Inseparable x y ∨ Disjoint (𝓝 x) (𝓝 y) :=
  r1Space_iff_inseparable_or_disjoint_nhds

example : LocallyCompactSpace Z ↔ ∀ (x : Z) (N : Set Z),
    N ∈ 𝓝 x → ∃ K ∈ 𝓝 x, K ⊆ N ∧ IsCompact K :=
  ⟨fun h => h.local_compact_nhds, fun h => ⟨h⟩⟩

example : CompactSpace Z ↔ IsCompact (univ : Set Z) :=
  ⟨fun h => h.isCompact_univ, fun h => ⟨h⟩⟩

example (A : Set Z) : Dense A ↔ ∀ x, x ∈ closure A := Iff.rfl

example (A : Set Z) : Dense A ↔
    ∀ U, IsOpen U → U.Nonempty → (U ∩ A).Nonempty := dense_iff_inter_open

example (A : Set Z) : IsGδ A ↔ ∃ T : Set (Set Z),
    (∀ U ∈ T, IsOpen U) ∧ T.Countable ∧ A = ⋂₀ T := Iff.rfl

example (A : Set Z) : IsGδ A ↔
    ∃ D : ℕ → Set Z, (∀ n, IsOpen (D n)) ∧ A = ⋂ n, D n :=
  isGδ_iff_eq_iInter_nat

example (A : Set Z) : IsCompact A ↔ ∀ (f : Filter Z),
    NeBot f → f ≤ 𝓟 A → ∃ x ∈ A, ClusterPt x f := by
  constructor
  · intro h f hf hA
    exact @h f hf hA
  · intro h f hf hA
    exact h f hf hA

example (x y : Z) : Specializes x y ↔ 𝓝 x ≤ 𝓝 y := Iff.rfl
example (x : Z) (f : Filter Z) : ClusterPt x f ↔ NeBot (𝓝 x ⊓ f) := Iff.rfl

-- Distinct labels must be disjoint even when their images are equal.
example {A : Type v} (F : Set A) (f : A → Set Z) :
    F.PairwiseDisjoint f ↔
      ∀ ⦃a⦄, a ∈ F → ∀ ⦃b⦄, b ∈ F → a ≠ b → Disjoint (f a) (f b) := Iff.rfl

-- Compact alone supplies only weak local compactness; R1 permits the upgrade.
example [CompactSpace Z] : WeaklyLocallyCompactSpace Z := inferInstance
example [R1Space Z] [CompactSpace Z] : LocallyCompactSpace Z := inferInstance

-- Compact subsets are not assumed closed in an R1 space.
example [R1Space Z] {K : Set Z} (hK : IsCompact K) : IsCompact (closure K) := hK.closure

example [R1Space Z] [LocallyCompactSpace Z] {V : Set Z}
    (ho : IsOpen V) (hn : V.Nonempty) :
    ∃ K : PositiveCompacts Z, closure (K : Set Z) ⊆ V :=
  ho.exists_positiveCompacts_closure_subset hn

example (K : ℕ → Set Z) (hstep : ∀ n, K (n + 1) ⊆ K n)
    (hne : ∀ n, (K n).Nonempty) (hc : IsCompact (K 0))
    (hclosed : ∀ n, IsClosed (K n)) : (⋂ n, K n).Nonempty :=
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hstep hne hc hclosed

example (x y : Z) : Inseparable x y ↔ 𝓝 x = 𝓝 y := Iff.rfl

example (x y : Z) : Inseparable x y ↔
    ∀ U : Set Z, IsOpen U → (x ∈ U ↔ y ∈ U) := inseparable_iff_forall_isOpen

example (x : Z) (N : Set Z) : N ∈ 𝓝 x ↔
    ∃ U ⊆ N, IsOpen U ∧ x ∈ U := mem_nhds_iff

example (A : Set Z) : IsCompact A ↔ ∀ {ι : Type u} (U : ι → Set Z),
    (∀ i, IsOpen (U i)) → (A ⊆ ⋃ i, U i) → ∃ t : Finset ι, A ⊆ ⋃ i ∈ t, U i :=
  isCompact_iff_finite_subcover

example (K : PositiveCompacts Z) : IsCompact (K : Set Z) ∧ (interior (K : Set Z)).Nonempty :=
  ⟨K.isCompact, K.interior_nonempty⟩

end MaterialImportedDefinitions
-- END material-imported-definition audit
