module
public import StrongChallenge
public section
open Set Function
-- BEGIN material-imported-definition audit
example {X : Type*} (f : X → X) (U V : Set X) (n : ℕ) :
    Furstenberg.Hit f U V n ↔ ∃ x, x ∈ U ∧ f^[n] x ∈ V := Iff.rfl
example {X : Type*} [TopologicalSpace X] (f : X → X) :
    Furstenberg.Transitive f ↔ ∀ U V : Set X, IsOpen U → U.Nonempty →
      IsOpen V → V.Nonempty → ∃ n, ∃ x, x ∈ U ∧ f^[n] x ∈ V := Iff.rfl
example {X : Type*} [TopologicalSpace X] (f : X → X) :
    Furstenberg.WeakMixing f ↔ Furstenberg.Transitive (fun p : X × X => (f p.1, f p.2)) :=
  Furstenberg.weakMixing_iff_product_transitive f
example {X : Type*} (f : X → X) (p : X × X) : Furstenberg.pairMap f p = (f p.1, f p.2) := rfl
example {X ι : Type*} (f : X → X) (x : ι → X) (i : ι) :
    Furstenberg.diagonal f ι x i = f (x i) := rfl
example {X : Type*} (f : X → X) (x : X) : f^[0] x = x := rfl
example {X : Type*} (f : X → X) (n : ℕ) (x : X) : f^[n+1] x = f^[n] (f x) := rfl
example {X : Type*} [t : TopologicalSpace X] :
    (inferInstance : TopologicalSpace (X × X)) =
      TopologicalSpace.induced Prod.fst t ⊓ TopologicalSpace.induced Prod.snd t := rfl
example {X ι : Type*} [t : TopologicalSpace X] :
    (inferInstance : TopologicalSpace (ι → X)) =
      ⨅ i : ι, TopologicalSpace.induced (fun x : ι → X => x i) t := rfl
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := continuous_def
example {X : Type*} : Nonempty X ↔ ∃ _x : X, True :=
  ⟨fun ⟨x⟩ => ⟨x, trivial⟩, fun ⟨x, _⟩ => ⟨x⟩⟩
example (k : ℕ) (i : Fin k) : i.val < k := i.isLt
example {ι : Type*} (s : Finset ι) : (s : Set ι).Finite := s.finite_toSet
example {X ι : Type*} (f : X → X) (U V : ι → Set X) :
    ∃ n : ℕ, ∀ i ∈ (∅ : Finset ι), Furstenberg.Hit f (U i) (V i) n :=
  ⟨0, by simp⟩
example {X : Type*} [TopologicalSpace X] (f : X → X) :
    Furstenberg.Transitive (Furstenberg.diagonal f (Fin 0)) := by
  intro U V _hU hnU _hV hnV
  obtain ⟨x, hx⟩ := hnU
  obtain ⟨y, hy⟩ := hnV
  refine ⟨0, x, hx, ?_⟩
  have he : x = y := Subsingleton.elim _ _
  simpa only [iterate_zero_apply, he] using hy

example {X : Type*} [TopologicalSpace X] (f : X → X) (x : X) :
    StrongTransitive.DenseOrbit f x ↔ Dense (Set.range (fun n : ℕ => f^[n] x)) := Iff.rfl
example {X : Type*} (k : ℕ) (x : ℕ → X) (i : Fin k) :
    StrongTransitive.initialSegment k x i = x i.val := rfl
example {X : Type*} [TopologicalSpace X] (f : X → X) (x : ℕ → X) :
    StrongTransitive.StrongSequence f x ↔ ∀ k : ℕ,
      Dense (Set.range (fun n : ℕ => (Furstenberg.diagonal f (Fin k))^[n]
        (fun i : Fin k => x i.val))) := Iff.rfl
example {X : Type*} [TopologicalSpace X] (f : X → X) (x : ℕ → X) :
    StrongTransitive.DenseOrbit (Furstenberg.diagonal f (Fin 0))
      (StrongTransitive.initialSegment 0 x) := by
  change DenseRange (fun n : ℕ => (Furstenberg.diagonal f (Fin 0))^[n]
    (StrongTransitive.initialSegment 0 x))
  apply Function.Surjective.denseRange
  intro y
  exact ⟨0, Subsingleton.elim _ _⟩
example {X : Type*} [TopologicalSpace X] (A : Set X) : A ∈ residual X ↔
    ∃ S : Set (Set X), (∀ U ∈ S, IsOpen U) ∧ (∀ U ∈ S, Dense U) ∧
      S.Countable ∧ ⋂₀ S ⊆ A := mem_residual_iff
example {X : Type*} [TopologicalSpace X] [BaireSpace X] {A : Set X}
    (h : A ∈ residual X) : Dense A := dense_of_mem_residual h
example {X : Type*} [TopologicalSpace X] [PolishSpace X] :
    SecondCountableTopology X := inferInstance
example {X : Type*} [TopologicalSpace X] [PolishSpace X] :
    TopologicalSpace.IsCompletelyMetrizableSpace X := inferInstance
example {X : Type*} [TopologicalSpace X] [PolishSpace X] :
    BaireSpace (ℕ → X) := inferInstance
example {X : Type*} [TopologicalSpace X] (C : Set X) :
    IsGδ C ↔ ∃ T : Set (Set X), (∀ U ∈ T, IsOpen U) ∧ T.Countable ∧ C = ⋂₀ T := Iff.rfl
example {X : Type*} [TopologicalSpace X] (C : Set X) :
    Dense C ↔ ∀ x, x ∈ closure C := Iff.rfl
example {X : Type*} (f : ℕ → X) (x : X) : x ∈ Set.range f ↔ ∃ n, f n = x := Iff.rfl
-- END material-imported-definition audit
