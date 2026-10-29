module
public import IPSolution

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
