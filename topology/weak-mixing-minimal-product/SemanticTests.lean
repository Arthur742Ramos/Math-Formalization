module
public import ProductSolution
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

example (S : Set ℕ) : WeakMinimal.Thick S ↔ ∀ L N : ℕ, ∃ m, N ≤ m ∧ ∀ j ≤ L, m+j ∈ S := Iff.rfl
example (S : Set ℕ) : WeakMinimal.Syndetic S ↔ ∃ K : ℕ, ∀ k, ∃ j ≤ K, k+j ∈ S := Iff.rfl
example {X : Type*} [TopologicalSpace X] (f : X → X) :
    WeakMinimal.Minimal f ↔ ∀ x, Dense (range (fun n : ℕ => f^[n] x)) := Iff.rfl
example {X Y : Type*} (f : X → X) (g : Y → Y) (p : X × Y) :
    WeakMinimal.productMap f g p = (f p.1,g p.2) := rfl
example {X : Type*} [TopologicalSpace X] (S : Set X) : Dense S ↔ ∀ x, x ∈ closure S := Iff.rfl
example {X Y : Type*} (f : X → Y) : Surjective f ↔ ∀ y, ∃ x, f x = y := Iff.rfl
example {X : Type*} [TopologicalSpace X] [CompactSpace X] : IsCompact (univ : Set X) := isCompact_univ
example {X : Type*} [TopologicalSpace X] [T2Space X] {x y : X} (h : x ≠ y) :
    ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B := t2_separation h
example {X : Type*} (f : ℕ → X) (x : X) : x ∈ Set.range f ↔ ∃ n, f n = x := Iff.rfl
-- END material-imported-definition audit

example {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] :
    (inferInstance : TopologicalSpace (X × Y)) =
      TopologicalSpace.induced Prod.fst tX ⊓ TopologicalSpace.induced Prod.snd tY := rfl
