module
public import HSChallenge
public section
open Set Filter TopologicalSpace
open scoped Topology symmDiff
#check HewittSavage.category_zero_one
#check HewittSavage.polish_sequence_zero_one
example {J X : Type*} [Infinite J] [TopologicalSpace X] [BaireSpace (J → X)]
    {A : Set (J → X)} (hA : BaireMeasurableSet A)
    (hinv : ∀ σ : Equiv.Perm J, {j | σ j ≠ j}.Finite → ∀ x, x ∈ A ↔ x ∘ σ ∈ A) :
    IsMeagre A ∨ IsMeagre Aᶜ := HewittSavage.category_zero_one hA hinv
example {X : Type*} [TopologicalSpace X] [PolishSpace X] {A : Set (ℕ → X)}
    (hA : BaireMeasurableSet A)
    (hinv : ∀ σ : Equiv.Perm ℕ, {j | σ j ≠ j}.Finite → ∀ x, x ∈ A ↔ x ∘ σ ∈ A) :
    IsMeagre A ∨ IsMeagre Aᶜ := HewittSavage.polish_sequence_zero_one hA hinv

-- BEGIN material-imported-definition audit
example {J : Type*} (σ : Equiv.Perm J) :
    HewittSavage.FiniteMoves σ ↔ {j | σ j ≠ j}.Finite := Iff.rfl
example {J : Type*} : Equiv.Perm J = (J ≃ J) := rfl
example {J : Type*} : Finite J ↔ ∃ n, Nonempty (J ≃ Fin n) := finite_iff_exists_equiv_fin
example {J : Type*} [Infinite J] : ¬ Finite J := Infinite.not_finite
example {J : Type*} : Infinite J ↔ ¬ Finite J := not_finite_iff_infinite.symm
example {J : Type*} (s : Set J) : s.Finite ↔ Finite s := Iff.rfl
example {J : Type*} (s : Set J) : s.Finite ↔ Nonempty (Fintype s) := Set.finite_def
example {J X : Type*} [t : TopologicalSpace X] :
    (inferInstance : TopologicalSpace (J → X)) =
      ⨅ j : J, TopologicalSpace.induced (fun x : J → X => x j) t := rfl
example {J X : Type*} [TopologicalSpace X] (j : J) : Continuous (fun x : J → X => x j) :=
  continuous_apply j
example {J X : Type*} [TopologicalSpace X] (σ : Equiv.Perm J) (x : J → X) :
    HewittSavage.reindexHomeomorph σ x = x ∘ σ := rfl
example {X : Type*} [TopologicalSpace X] [BaireSpace X] {U : Set X}
    (ho : IsOpen U) (hne : U.Nonempty) : ¬ IsMeagre U := not_isMeagre_of_isOpen ho hne
example {X : Type*} [TopologicalSpace X] [PolishSpace X] : PolishSpace (ℕ → X) := inferInstance
example {X : Type*} [TopologicalSpace X] [PolishSpace X] : BaireSpace (ℕ → X) := inferInstance
example {X : Type*} [TopologicalSpace X] (A : Set X) : IsMeagre A ↔ Aᶜ ∈ residual X := Iff.rfl
example {X : Type*} [TopologicalSpace X] (A : Set X) : IsNowhereDense A ↔ interior (closure A) = ∅ := Iff.rfl
example {X : Type*} [TopologicalSpace X] (A : Set X) : A ∈ residual X ↔
    ∃ S : Set (Set X), (∀ U ∈ S, IsOpen U) ∧ (∀ U ∈ S, Dense U) ∧
      S.Countable ∧ ⋂₀ S ⊆ A := mem_residual_iff
example {X : Type*} [TopologicalSpace X] (A : Set X) :
    BaireMeasurableSet A ↔
      @MeasurableSet X (eventuallyMeasurableSpace (borel X) (residual X)) A := Iff.rfl
example {X : Type*} [TopologicalSpace X] (A : Set X) :
    BaireMeasurableSet A ↔ ∃ O : Set X, IsOpen O ∧ IsMeagre (A ∆ O) := by
  rw [BaireMeasurableSet.iff_residualEq_isOpen]
  constructor
  · rintro ⟨O, hO, hAO⟩
    refine ⟨O, hO, ?_⟩
    change ∀ᶠ x in residual X, x ∉ A ∆ O
    filter_upwards [hAO.mem_iff] with x hx
    simp only [mem_symmDiff]
    tauto
  · rintro ⟨O, hO, hAO⟩
    refine ⟨O, hO, Filter.eventuallyEqSet_iff.mpr ?_⟩
    change ∀ᶠ x in residual X, x ∉ A ∆ O at hAO
    filter_upwards [hAO] with x hx
    simp only [mem_symmDiff] at hx
    tauto
example {X : Type*} [TopologicalSpace X] [PolishSpace X] :
    ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace X) ∧
      @CompleteSpace X m.toUniformSpace := IsCompletelyMetrizableSpace.complete
-- END material-imported-definition audit
