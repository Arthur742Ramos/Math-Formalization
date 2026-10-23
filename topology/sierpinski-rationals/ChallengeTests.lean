module
public import SRChallenge
@[expose] public section
noncomputable section
open Set Function Filter Topology TopologicalSpace
open SierpinskiRationals
-- BEGIN material-imported-definition audit
example {X : Type*} [TopologicalSpace X] :
    Nonempty (X ≃ₜ ℚ) ↔ Nonempty X ∧ Countable X ∧ MetrizableSpace X ∧ PerfectSpace X :=
  nonempty_homeomorph_iff X
example {X : Type*} [TopologicalSpace X] :
    PerfectSpace X ↔ ∀ x : X, Filter.NeBot (𝓝[≠] x) := perfectSpace_iff_forall_not_isolated
example {X : Type*} [TopologicalSpace X] (C : Set X) :
    Preperfect C ↔ ∀ x ∈ C, ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ C, y ≠ x := preperfect_iff_nhds
example {X : Type*} [TopologicalSpace X] [MetrizableSpace X] :
    PseudoMetrizableSpace X ∧ T0Space X := ⟨inferInstance, inferInstance⟩
example {X : Type*} [t : TopologicalSpace X] [PseudoMetrizableSpace X] :
    ∃ u : UniformSpace X, u.toTopologicalSpace = t ∧
      @Filter.IsCountablyGenerated (X × X) (@uniformity X u) :=
  PseudoMetrizableSpace.exists_countably_generated
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Bijective e ∧ Continuous e ∧ Continuous e.symm :=
  ⟨e.bijective, e.continuous, e.symm.continuous⟩
example {X : Type*} [TopologicalSpace X] :
    HasClopenBasis X ↔ IsTopologicalBasis {U : Set X | IsClopen U} := Iff.rfl
example {X : Type*} [TopologicalSpace X] (U : Set X) :
    IsClopen U ↔ IsClosed U ∧ IsOpen U := Iff.rfl
example {X : Type*} [TopologicalSpace X] (B : Set (Set X)) (h : IsTopologicalBasis B) :
    ∀ U, IsOpen U ↔ ∀ x ∈ U, ∃ V ∈ B, x ∈ V ∧ V ⊆ U := fun _ => h.isOpen_iff
example {X : Type*} [TopologicalSpace X] {B : ℕ → Set X} {E : ℕ → X}
    [T2Space X] (S : BinaryScheme X B E) (hB : IsTopologicalBasis (range B)) (hE : Surjective E) :
    @OrderTopology X _ (S.codeOrder hB).toPreorder := S.codeOrder_topology hB hE
example : (inferInstance : TopologicalSpace ℚ) =
    TopologicalSpace.induced ((↑) : ℚ → ℝ) (inferInstance : TopologicalSpace ℝ) := rfl
example : Nonempty (ℚ ≃ₜ ℚ) := ⟨Homeomorph.refl _⟩
example : Nonempty ((ℚ × ℚ) ≃ₜ ℚ) := by
  have := rat_perfectSpace
  have hp : PerfectSpace (ℚ × ℚ) := by
    constructor
    rw [preperfect_iff_nhds]
    intro x _ U hU
    obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hU
    obtain ⟨y, hy, hyx⟩ := preperfect_iff_nhds.mp PerfectSpace.univ_preperfect
      x.1 (mem_univ _) V hV
    exact ⟨(y, x.2), ⟨hVW ⟨hy.1, mem_of_mem_nhds hW⟩, mem_univ _⟩,
      fun h => hyx (congrArg Prod.fst h)⟩
  exact nonempty_homeomorph _
example : ¬ Nonempty (Empty ≃ₜ ℚ) := by
  rintro ⟨e⟩
  exact Empty.elim (e.symm 0)
example : ¬ PerfectSpace Unit := by
  intro h
  obtain ⟨y, _, hy⟩ := preperfect_iff_nhds.mp h.univ_preperfect () (mem_univ _) univ (by simp)
  exact hy (Subsingleton.elim _ _)
example : ¬ Nonempty (Unit ≃ₜ ℚ) := by
  intro h
  have hp := ((nonempty_homeomorph_iff Unit).mp h).2.2.2
  obtain ⟨y, _, hy⟩ := preperfect_iff_nhds.mp hp.univ_preperfect () (mem_univ _) univ (by simp)
  exact hy (Subsingleton.elim _ _)
example {X : Type*} [TopologicalSpace X] [T2Space X] {B : ℕ → Set X} {E : ℕ → X}
    (S : BinaryScheme X B E) (hB : IsTopologicalBasis (range B)) (x y : X) :
    @LT.lt X (S.codeOrder hB).toLT x y ↔ toLex (S.code x) < toLex (S.code y) := Iff.rfl
example {X : Type*} [Preorder X] (a b x : X) :
    (x ∈ Iio b ↔ x < b) ∧ (x ∈ Ioi a ↔ a < x) ∧
      (x ∈ Ioo a b ↔ a < x ∧ x < b) := ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩
-- END material-imported-definition audit
