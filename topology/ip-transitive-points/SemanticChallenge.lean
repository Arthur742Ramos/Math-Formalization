module
public import IPChallenge

@[expose] public section
open Set Function Filter
open scoped Topology BigOperators

example : ¬ IPTransitive.HasPositiveFiniteSums (∅ : Set ℕ) := by
  rintro ⟨p, hp, h⟩
  have h0 := h {0} (by simp)
  simp at h0

example : ¬ IPTransitive.HasPositiveFiniteSums ({0} : Set ℕ) := by
  rintro ⟨p, hp, h⟩
  have h0 := h {0} (by simp)
  have hz : p 0 = 0 := by simpa using h0
  have hpos := hp 0
  omega

example (A : Set ℕ) (h : IPTransitive.HasPositiveFiniteSums A) :
    ∃ n ∈ A, 0 < n := by
  obtain ⟨p, hp, hsum⟩ := h
  refine ⟨p 0, ?_, hp 0⟩
  simpa using hsum {0} (by simp)

example (f : PUnit → PUnit) (U : Set PUnit) (hU : U.Nonempty) :
    IPTransitive.HasPositiveFiniteSums {n | f^[n] PUnit.unit ∈ U} :=
  IPTransitive.singleton_visits_have_positive_finite_sums f PUnit.unit U hU

example (A : Set ℕ) (h : IPTransitive.HasPositiveFiniteSums A) :
    ∃ p : ℕ → ℕ, (∀ i, 0 < p i) ∧ p 0 + p 1 ∈ A := by
  obtain ⟨p, hp, hs⟩ := h
  refine ⟨p, hp, ?_⟩
  simpa using hs {0, 1} (by simp)

example : ¬ IPTransitive.HasPositiveFiniteSums ({1} : Set ℕ) := by
  rintro ⟨p, hp, hs⟩
  have h0 : p 0 = 1 := by simpa using hs {0} (by simp)
  have h1 : p 1 = 1 := by simpa using hs {1} (by simp)
  have h01 := hs {0, 1} (by simp)
  simp [h0, h1] at h01

example (f : ℕ → ℕ) : IPTransitive.pairMap f (2, 3) = (f 2, f 3) := rfl

example : IPTransitive.OpenTransitive (IPTransitive.pairMap (id : PUnit → PUnit)) := by
  intro U V hU ⟨u, hu⟩ hV ⟨v, hv⟩
  refine ⟨0, u, hu, ?_⟩
  change u ∈ V
  have huv : u = v := Subsingleton.elim u v
  subst u
  exact hv

example : ∃ C : Set PUnit, IsGδ C ∧ Dense C ∧ C.Nonempty ∧
    ∀ x ∈ C, IPTransitive.IsIPTransitivePoint (id : PUnit → PUnit) x := by
  apply IPTransitive.exists_dense_Gdelta_ip_transitive (id : PUnit → PUnit) continuous_id
  intro U V hU ⟨u, hu⟩ hV ⟨v, hv⟩
  refine ⟨0, u, hu, ?_⟩
  change u ∈ V
  have huv : u = v := Subsingleton.elim u v
  subst u
  exact hv

/-- Concrete non-singleton system exercising the positive-return-to-IP lemma. -/
example : IPTransitive.HasPositiveFiniteSums
    {n | ((fun _ : Bool => true)^[n]) true ∈ ({true} : Set Bool)} := by
  have hc : Continuous (fun _ : Bool => true) := continuous_const
  have ho : IsOpen ({true} : Set Bool) := isOpen_discrete _
  have hy : true ∈ ({true} : Set Bool) := by simp
  apply IPTransitive.positive_pair_returns_yield_ip (fun _ : Bool => true) hc
    true true ({true} : Set Bool) ho hy
  intro V hV hyV
  refine ⟨1, by decide, ?_, ?_⟩ <;> simpa using hyV

example : {n : ℕ | ∃ z ∈ (Set.univ : Set (PUnit × PUnit)),
    (IPTransitive.pairMap (id : PUnit → PUnit))^[n] z ∈ Set.univ}.Infinite := by
  have ht : IPTransitive.OpenTransitive (IPTransitive.pairMap (id : PUnit → PUnit)) := by
    intro U V hU ⟨u, hu⟩ hV ⟨v, hv⟩
    refine ⟨0, u, hu, ?_⟩
    change u ∈ V
    have huv : u = v := Subsingleton.elim u v
    subst u
    exact hv
  exact IPTransitive.weak_mixing_infinite_hits (id : PUnit → PUnit) continuous_id ht
    Set.univ Set.univ isOpen_univ Set.univ_nonempty isOpen_univ Set.univ_nonempty

-- BEGIN material-imported-definition audit
example {X : Type*} [t : TopologicalSpace X] :
    (inferInstance : TopologicalSpace (X × X)) =
      TopologicalSpace.induced Prod.fst t ⊓ TopologicalSpace.induced Prod.snd t := rfl
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := continuous_def
example {X : Type*} [TopologicalSpace X] (f : X → X) :
    IPTransitive.OpenTransitive f ↔ ∀ U V : Set X, IsOpen U → U.Nonempty →
      IsOpen V → V.Nonempty → ∃ n : ℕ, ∃ z ∈ U, f^[n] z ∈ V := Iff.rfl
example {X : Type*} (f : X → X) (p : X × X) :
    IPTransitive.pairMap f p = (f p.1, f p.2) := rfl
example {X : Type*} (f : X → X) (x : X) : f^[0] x = x := rfl
example {X : Type*} (f : X → X) (n : ℕ) (x : X) : f^[n+1] x = f^[n] (f x) := rfl
example {X : Type*} (s : Set X) : s.Nonempty ↔ ∃ x, x ∈ s := Iff.rfl
example {X : Type*} (s : Finset X) : s.Nonempty ↔ ∃ x, x ∈ s := Iff.rfl
example (s : Set ℕ) : s.Infinite ↔ ¬ s.Finite := Iff.rfl
example (p : ℕ → ℕ) : (∑ i ∈ ({0, 1} : Finset ℕ), p i) = p 0 + p 1 := by simp
example (A : Set ℕ) : IPTransitive.HasPositiveFiniteSums A ↔
    ∃ p : ℕ → ℕ, (∀ i, 0 < p i) ∧ ∀ s : Finset ℕ, s.Nonempty → (∑ i ∈ s, p i) ∈ A := Iff.rfl
example {X : Type*} [TopologicalSpace X] (f : X → X) (x : X) :
    IPTransitive.IsIPTransitivePoint f x ↔ ∀ U : Set X, IsOpen U → U.Nonempty →
      IPTransitive.HasPositiveFiniteSums {n | f^[n] x ∈ U} := Iff.rfl
example {X : Type*} [TopologicalSpace X] (A : Set X) : A ∈ residual X ↔
    ∃ S : Set (Set X), (∀ U ∈ S, IsOpen U) ∧ (∀ U ∈ S, Dense U) ∧
      S.Countable ∧ ⋂₀ S ⊆ A := mem_residual_iff
example {X : Type*} [TopologicalSpace X] (C : Set X) :
    IsGδ C ↔ ∃ T : Set (Set X), (∀ U ∈ T, IsOpen U) ∧ T.Countable ∧ C = ⋂₀ T := Iff.rfl
example {X : Type*} [TopologicalSpace X] (C : Set X) :
    Dense C ↔ ∀ x, x ∈ closure C := Iff.rfl
example {X : Type*} [TopologicalSpace X] [T2Space X] {x y : X} (h : x ≠ y) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V := t2_separation h
example (s : Finset ℕ) (p : ℕ → ℕ) :
    (∑ i ∈ s, p i) = (s.val.map p).sum := rfl
example (s : Set ℕ) : s.Infinite ↔ ∀ N, ∃ n ≥ N, n ∈ s := by
  change {n : ℕ | n ∈ s}.Infinite ↔ ∀ N, ∃ n ≥ N, n ∈ s
  rw [← Nat.frequently_atTop_iff_infinite, frequently_atTop]
example (α : Type*) : Finite α ↔ ∃ n : ℕ, Nonempty (α ≃ Fin n) :=
  finite_iff_exists_equiv_fin
example (α : Type*) : Nonempty α ↔ ∃ x : α, x = x := by
  constructor
  · rintro ⟨x⟩; exact ⟨x, rfl⟩
  · rintro ⟨x, _⟩; exact ⟨x⟩
-- END material-imported-definition audit
