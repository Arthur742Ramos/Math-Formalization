module
public import BCSolution
@[expose] public section
open Set Function Filter Topology TopologicalSpace
open BaireCharacterization
-- BEGIN material-imported-definition audit
example {X : Type*} [TopologicalSpace X] :
    HasClopenBasis X ↔ IsTopologicalBasis {U : Set X | IsClopen U} := Iff.rfl
example {X : Type*} [TopologicalSpace X] :
    CompactInteriorEmpty X ↔ ∀ K : Set X, IsCompact K → interior K = ∅ := Iff.rfl
example {X : Type*} [TopologicalSpace X] (U : Set X) :
    IsClopen U ↔ IsClosed U ∧ IsOpen U := Iff.rfl
example {X : Type*} [TopologicalSpace X] (B : Set (Set X)) (h : IsTopologicalBasis B) :
    ∀ U, IsOpen U ↔ ∀ x ∈ U, ∃ V ∈ B, x ∈ V ∧ V ⊆ U := fun _ => h.isOpen_iff
example {X : Type*} [TopologicalSpace X] (K : Set X) :
    interior K = ⋃₀ {V | IsOpen V ∧ V ⊆ K} := rfl
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Bijective e ∧ Continuous e ∧ Continuous e.symm :=
  ⟨e.bijective, e.continuous, e.symm.continuous⟩
example {X : Type*} [TopologicalSpace X] :
    Nonempty (X ≃ₜ (ℕ → ℕ)) ↔ Nonempty X ∧ PolishSpace X ∧
      HasClopenBasis X ∧ CompactInteriorEmpty X := nonempty_homeomorph_iff X
example : Nonempty ((ℕ → ℕ) ≃ₜ (ℕ → ℕ)) := ⟨Homeomorph.refl _⟩
example : ¬ Nonempty (Empty ≃ₜ (ℕ → ℕ)) := by
  rintro ⟨e⟩
  exact Empty.elim (e.symm (fun _ => 0))
example : ¬ CompactInteriorEmpty Unit := by
  intro h
  have he := h univ isCompact_univ
  simp at he
example (x z : ℕ → ℕ) (n : ℕ) :
    z ∈ PiNat.cylinder x n ↔ ∀ i < n, z i = x i := Iff.rfl
example (x : ℕ → ℕ) (n : ℕ) : PiNat.res x (n+1) = x n :: PiNat.res x n := rfl
example {X : Type*} (A : List ℕ → Set X) (x : ℕ → ℕ) :
    x ∈ (CantorScheme.inducedMap A).1 ↔ (⋂ n, A (PiNat.res x n)).Nonempty := Iff.rfl
example {X : Type*} (A : List ℕ → Set X) :
    CantorScheme.Disjoint A ↔ ∀ l, Pairwise (fun a b => Disjoint (A (a :: l)) (A (b :: l))) := Iff.rfl
example {X : Type*} [t : TopologicalSpace X] [PolishSpace X] :
    ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧
      @CompleteSpace X m.toUniformSpace := IsCompletelyMetrizableSpace.complete
example {X : Type*} [TopologicalSpace X] [PolishSpace X] : SecondCountableTopology X := inferInstance
example : DiscreteTopology ℕ := inferInstance
example : (inferInstance : TopologicalSpace (ℕ → ℕ)) =
    ⨅ i : ℕ, TopologicalSpace.induced (fun f : ℕ → ℕ => f i)
      (inferInstance : TopologicalSpace ℕ) := rfl
example {X : Type u} [TopologicalSpace X] (K : Set X) :
    IsCompact K ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → K ⊆ ⋃ i, U i → ∃ t : Finset ι, K ⊆ ⋃ i ∈ t, U i :=
  isCompact_iff_finite_subcover
example {X : Type*} [MetricSpace X] (K : Set X) :
    TotallyBounded K ↔ ∀ ε > (0 : ℝ), ∃ t : Set X, t.Finite ∧ K ⊆ ⋃ y ∈ t, Metric.ball y ε :=
  Metric.totallyBounded_iff
example {X : Type*} (U V : Set X) : Disjoint U V ↔ U ∩ V = ∅ :=
  Set.disjoint_iff_inter_eq_empty
example {J : Type*} (r : J → J → Prop) :
    Pairwise r ↔ ∀ ⦃i j⦄, i ≠ j → r i j := Iff.rfl
example (J : Type*) : Infinite J ↔ ¬ Finite J := not_finite_iff_infinite.symm
example (J : Type*) : Finite J ↔ ∃ n, Nonempty (J ≃ Fin n) := finite_iff_exists_equiv_fin
-- END material-imported-definition audit
