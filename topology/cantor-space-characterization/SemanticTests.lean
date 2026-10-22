module
public import CSSolution
@[expose] public section
noncomputable section
open Set Function Filter Topology TopologicalSpace
open CantorCharacterization
-- BEGIN material-imported-definition audit
example {X : Type*} [TopologicalSpace X] :
    HasClopenBasis X ↔ IsTopologicalBasis {U : Set X | IsClopen U} := Iff.rfl
example {X : Type*} [TopologicalSpace X] (U : Set X) :
    IsClopen U ↔ IsClosed U ∧ IsOpen U := Iff.rfl
example {X : Type*} [TopologicalSpace X] (B : Set (Set X)) (h : IsTopologicalBasis B) :
    ∀ U, IsOpen U ↔ ∀ x ∈ U, ∃ V ∈ B, x ∈ V ∧ V ⊆ U := fun _ => h.isOpen_iff
example {X : Type*} [TopologicalSpace X] :
    PerfectSpace X ↔ ∀ x : X, Filter.NeBot (𝓝[≠] x) := perfectSpace_iff_forall_not_isolated
example {X : Type*} [TopologicalSpace X] (C : Set X) :
    Preperfect C ↔ ∀ x ∈ C, ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ C, y ≠ x := preperfect_iff_nhds
example {X : Type*} [TopologicalSpace X] (x : X) (f : Filter X) :
    AccPt x f ↔ Filter.NeBot (𝓝[≠] x ⊓ f) := Iff.rfl
example {X : Type*} [TopologicalSpace X] (x : X) (U : Set X) :
    nhdsWithin x U = 𝓝 x ⊓ 𝓟 U := rfl
example {X : Type*} [TopologicalSpace X] [CompactSpace X] :
    IsCompact (univ : Set X) := isCompact_univ
example {X : Type u} [TopologicalSpace X] (K : Set X) :
    IsCompact K ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → K ⊆ ⋃ i, U i → ∃ t : Finset ι, K ⊆ ⋃ i ∈ t, U i :=
  isCompact_iff_finite_subcover
example {X : Type*} [TopologicalSpace X] [MetrizableSpace X] :
    PseudoMetrizableSpace X ∧ T0Space X := ⟨inferInstance, inferInstance⟩
example {X : Type*} [t : TopologicalSpace X] [PseudoMetrizableSpace X] :
    ∃ u : UniformSpace X, u.toTopologicalSpace = t ∧
      @Filter.IsCountablyGenerated (X × X) (@uniformity X u) :=
  PseudoMetrizableSpace.exists_countably_generated
example {X : Type*} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] :
    T2Space X ∧ SecondCountableTopology X := ⟨inferInstance, inferInstance⟩
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Bijective e ∧ Continuous e ∧ Continuous e.symm :=
  ⟨e.bijective, e.continuous, e.symm.continuous⟩
example {X : Type*} [TopologicalSpace X] (U V : Set X) :
    Disjoint U V ↔ U ∩ V = ∅ := Set.disjoint_iff_inter_eq_empty
example (x z : ℕ → Bool) (n : ℕ) :
    z ∈ PiNat.cylinder x n ↔ ∀ i < n, z i = x i := Iff.rfl
example (x : ℕ → Bool) (n : ℕ) :
    PiNat.res x (n+1) = x n :: PiNat.res x n := rfl
example : DiscreteTopology Bool := inferInstance
example : (inferInstance : TopologicalSpace (ℕ → Bool)) =
    ⨅ i : ℕ, TopologicalSpace.induced (fun f : ℕ → Bool => f i)
      (inferInstance : TopologicalSpace Bool) := rfl
example {X : Type*} [TopologicalSpace X] {B : ℕ → Set X}
    (S : BinaryScheme X B) (x : X) (n : ℕ) :
    S.code x n = S.next x (S.addressPrefix x n) := rfl
example {X : Type*} [TopologicalSpace X] {B : ℕ → Set X}
    (S : BinaryScheme X B) (x : X) (l : List Bool) :
    S.next x l = @decide (x ∈ S.sets (true :: l)) (Classical.propDecidable _) := rfl
example {X : Type*} [TopologicalSpace X] {B : ℕ → Set X}
    (S : BinaryScheme X B) :
    S.sets [] = univ ∧ ∀ l, S.sets (false :: l) ∪ S.sets (true :: l) = S.sets l :=
  ⟨S.root, S.cover⟩
example {X : Type*} [TopologicalSpace X] {B : ℕ → Set X}
    (S : BinaryScheme X B) :
    ∀ l b, S.sets (b :: l) ⊆ B l.length ∨ S.sets (b :: l) ⊆ (B l.length)ᶜ :=
  S.decides
example {X : Type*} [TopologicalSpace X] :
    Nonempty (X ≃ₜ (ℕ → Bool)) ↔ Nonempty X ∧ CompactSpace X ∧ MetrizableSpace X ∧
      HasClopenBasis X ∧ PerfectSpace X := nonempty_homeomorph_iff X
example : Nonempty ((ℕ → Bool) ≃ₜ (ℕ → Bool)) := ⟨Homeomorph.refl _⟩
example : ¬ Nonempty (Empty ≃ₜ (ℕ → Bool)) := by
  rintro ⟨e⟩
  exact Empty.elim (e.symm (fun _ => false))
example : ¬ PerfectSpace Unit := by
  intro h
  obtain ⟨y, _, hy⟩ := preperfect_iff_nhds.mp h.univ_preperfect ()
    (mem_univ _) univ (by simp)
  exact hy (Subsingleton.elim _ _)
example : ¬ Nonempty (Unit ≃ₜ (ℕ → Bool)) := by
  intro h
  have hp := ((nonempty_homeomorph_iff Unit).mp h).2.2.2.2
  obtain ⟨y, _, hy⟩ := preperfect_iff_nhds.mp hp.univ_preperfect ()
    (mem_univ _) univ (by simp)
  exact hy (Subsingleton.elim _ _)
-- END material-imported-definition audit
