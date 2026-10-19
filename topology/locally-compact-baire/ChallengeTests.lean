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
