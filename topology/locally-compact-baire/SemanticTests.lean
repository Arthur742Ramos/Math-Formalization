module
public import LCBSolution

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

-- Both empty-factor boundaries retain their advertised contracts.
example {Y : Type*} [TopologicalSpace Y] [R1Space Y] [LocallyCompactSpace Y] :
    BaireSpace (Empty × Y) := by
  have : BaireSpace Empty := baire_of_finite
  exact baireSpace_prod

example {X : Type*} [TopologicalSpace X] [BaireSpace X] :
    BaireSpace (X × Empty) := baireSpace_prod

-- A dense Gδ in an empty product cannot project densely onto a nonempty parameter space.
-- This checks why the nonempty fiber region in the projection theorem is essential.
example : ¬ ∃ G : Set Unit, Dense G ∧
    G ⊆ Prod.fst '' (univ : Set (Unit × Empty)) := by
  rintro ⟨G, hG, hsub⟩
  obtain ⟨x, hx⟩ := hG.nonempty
  obtain ⟨⟨_, y⟩, _, _⟩ := hsub hx
  exact isEmptyElim y

-- The first factor can be the non-Hausdorff Sierpinski space;
-- the compact R1 second factor can even be non-T0 (indiscrete Bool).
example : let : TopologicalSpace Bool := ⊤
    BaireSpace (Prop × Bool) := by
  let : TopologicalSpace Bool := ⊤
  have : BaireSpace Prop := baire_of_finite
  have : R1Space Bool := ⟨fun x y => Or.inl (by
    apply specializes_iff_nhds.mpr
    simp [nhds_top])⟩
  exact baireSpace_prod_of_compact

-- Distinct labels with the same inhabited projected open cannot both survive disjointness.
example {X : Type*} (f : Bool → Set X) (F : Set Bool) (h : F.PairwiseDisjoint f)
    (htrue : true ∈ F) (hfalse : false ∈ F) (heq : f true = f false)
    (hne : (f true).Nonempty) : False := by
  obtain ⟨x, hx⟩ := hne
  exact disjoint_left.mp (h htrue hfalse (by decide)) hx (heq ▸ hx)
