module
public import OBSolution
@[expose] public section
open Set Function
example {X : Type*} [TopologicalSpace X] [PolishSpace X] [Nonempty X] :
    ∃ f : (ℕ → ℕ) → X, Continuous f ∧ IsOpenMap f ∧ Surjective f :=
  OpenBaire.exists_continuous_open_surjective X
example : ¬ ∃ f : (ℕ → ℕ) → Empty, Continuous f ∧ IsOpenMap f ∧ Surjective f := by
  rintro ⟨f, _⟩
  exact Empty.elim (f (fun _ => 0))
example : ∃ f : (ℕ → ℕ) → Unit, Continuous f ∧ IsOpenMap f ∧ Surjective f :=
  OpenBaire.exists_continuous_open_surjective Unit
example {X : Type*} [MetricSpace X] [CompleteSpace X]
    (S : OpenBaire.OpenScheme X) (x : ℕ → ℕ) (n : ℕ) :
    S.limit '' PiNat.cylinder x n = S.sets (PiNat.res x n) :=
  S.image_cylinder x n

-- BEGIN material-imported-definition audit
open Filter Topology TopologicalSpace
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ U, IsOpen U → IsOpen (f ⁻¹' U) :=
  ⟨fun h => h.isOpen_preimage, fun h => ⟨h⟩⟩
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    IsOpenMap f ↔ ∀ U, IsOpen U → IsOpen (f '' U) := Iff.rfl
example {X Y : Type*} (f : X → Y) :
    Surjective f ↔ ∀ y, ∃ x, f x = y := Iff.rfl
example {X : Type*} (U : Set X) : U.Nonempty ↔ ∃ x, x ∈ U := Iff.rfl
example (x z : ℕ → ℕ) (n : ℕ) :
    z ∈ PiNat.cylinder x n ↔ ∀ i < n, z i = x i := Iff.rfl
example (x : ℕ → ℕ) (n : ℕ) : PiNat.res x (n+1) = x n :: PiNat.res x n := rfl
example {X : Type*} (A : List ℕ → Set X) (x : ℕ → ℕ) :
    x ∈ (CantorScheme.inducedMap A).1 ↔ (⋂ n, A (PiNat.res x n)).Nonempty := Iff.rfl
example {X : Type*} [TopologicalSpace X] (A : List ℕ → Set X) :
    CantorScheme.ClosureAntitone A ↔ ∀ l a, closure (A (a :: l)) ⊆ A l := Iff.rfl
example {X : Type*} [MetricSpace X] (A : List ℕ → Set X) :
    CantorScheme.VanishingDiam A ↔
      ∀ x, Tendsto (fun n => Metric.ediam (A (PiNat.res x n))) atTop (𝓝 0) := Iff.rfl
example {X : Type*} [t : TopologicalSpace X] [PolishSpace X] :
    ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧
      @CompleteSpace X m.toUniformSpace := IsCompletelyMetrizableSpace.complete
example {X : Type*} [TopologicalSpace X] [PolishSpace X] : SecondCountableTopology X :=
  inferInstance
example {X : Type*} [t : TopologicalSpace X] [SecondCountableTopology X] :
    ∃ b : Set (Set X), b.Countable ∧ t = TopologicalSpace.generateFrom b :=
  SecondCountableTopology.is_open_generated_countable
example : DiscreteTopology ℕ := inferInstance
example : (inferInstance : TopologicalSpace (ℕ → ℕ)) =
    ⨅ i : ℕ, TopologicalSpace.induced (fun f : ℕ → ℕ => f i)
      (inferInstance : TopologicalSpace ℕ) := rfl
-- END material-imported-definition audit
