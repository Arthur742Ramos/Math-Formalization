module
public import RecurrenceSolution

open Set Function Filter TopologicalSpace MultipleRecurrence
open scoped Topology

example (S : Set ℕ) (h : Syndetic S) (N : ℕ) :
    ∃ a, N ≤ a ∧ 0 < a ∧ ∃ b, b ∈ S := by
  obtain ⟨a, ha, hp, b, hb⟩ := syndetic_arithmetic_progressions_after S h 0 N
  exact ⟨a, ha, hp, b, by simpa using hb 0 (Nat.zero_le 0)⟩

example (f : PUnit → PUnit) (hf : Continuous f)
    (hm : ForwardMinimal f) (N : ℕ) :
    ∃ n, N ≤ n ∧ 0 < n ∧ ∃ x : PUnit, ∀ i ≤ 2, f^[i * n] x ∈ (univ : Set PUnit) := by
  obtain ⟨n, hn, hp, x, _, h⟩ :=
    minimal_multiple_recurrence_after f hf hm univ isOpen_univ ⟨PUnit.unit, trivial⟩ 2 N
  exact ⟨n, hn, hp, x, h⟩

example {X : Type*} [TopologicalSpace X] (f : X → X) (x : X)
    (hx : MultiplyRecurrent f x) (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) (N : ℕ) :
    ∃ n, N ≤ n ∧ 0 < n ∧ f^[n] x ∈ U ∧ f^[2*n] x ∈ U := by
  obtain ⟨n, hn, hp, h⟩ := hx U hU hxU 2 N
  exact ⟨n, hn, hp, by simpa using h 1 (by omega), h 2 le_rfl⟩

/-- The flip on two points has dense forward orbit at every point. -/
theorem bool_flip_minimal : ForwardMinimal Bool.not := by
  intro x
  have h : range (fun n : ℕ => Bool.not^[n] x) = univ := by
    ext y
    simp only [mem_range, mem_univ, iff_true]
    cases x <;> cases y <;> first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩
  rw [h]
  exact dense_univ

example (N : ℕ) : ∃ n, N ≤ n ∧ 0 < n ∧ ∃ x ∈ ({true} : Set Bool),
    ∀ i ≤ 3, Bool.not^[i * n] x ∈ ({true} : Set Bool) := by
  exact minimal_multiple_recurrence_after Bool.not continuous_of_discreteTopology
    bool_flip_minimal {true} (isOpen_discrete _) ⟨true, rfl⟩ 3 N

example {X : Type*} [TopologicalSpace X] (f : X → X) (x : X)
    (hx : MultiplyRecurrent f x) (U : Set X) (hU : IsOpen U) (hxU : x ∈ U)
    (N : ℕ) : ∃ n, N ≤ n ∧ 0 < n ∧ ∀ k ∈ ({0, 2, 5} : Finset ℕ),
      f^[k * n] x ∈ U :=
  finite_multipliers_return f x hx U hU hxU {0, 2, 5} N

/-- A zero-only time set cannot satisfy the positive-step contract. -/
example : ¬ ∃ n : ℕ, 0 < n ∧ n ∈ ({0} : Set ℕ) := by
  simp

example {X : Type*} [TopologicalSpace X] (f : X → X) (x : X)
    (hx : MultiplyRecurrent f x) (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ n, 10 ≤ n ∧ 0 < n ∧ ∀ k ∈ (∅ : Finset ℕ), f^[k * n] x ∈ U :=
  finite_multipliers_return f x hx U hU hxU ∅ 10
theorem singleton_id_minimal : ForwardMinimal (id : PUnit → PUnit) := by
  intro x
  have h : range (fun n : ℕ => (id : PUnit → PUnit)^[n] x) = univ := by
    ext y
    simp only [mem_range, mem_univ, iff_true]
    exact ⟨0, trivial⟩
  rw [h]
  exact dense_univ

example : ∃ C : Set PUnit, IsGδ C ∧ Dense C ∧ C.Nonempty ∧
    ∀ x ∈ C, MultiplyRecurrent (id : PUnit → PUnit) x :=
  exists_dense_Gdelta_multiply_recurrent id continuous_id singleton_id_minimal
-- BEGIN material-imported-definition audit
example {α : Type*} (a : α) (s : Finset α) : a ∈ s ↔ a ∈ s.val := Finset.mem_def
example {α β : Type*} (f : α → β) (y : β) : y ∈ range f ↔ ∃ x, f x = y := Iff.rfl
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := continuous_def
example {X : Type*} (f : X → X) (x : X) : f^[0] x = x := rfl
example {X : Type*} (f : X → X) (n : ℕ) (x : X) : f^[n+1] x = f^[n] (f x) := rfl
example {X : Type*} (s : Set X) : s.Nonempty ↔ ∃ x, x ∈ s := Iff.rfl
example {X : Type*} [TopologicalSpace X] (C : Set X) :
    Dense C ↔ ∀ x, x ∈ closure C := Iff.rfl
example {X : Type*} [TopologicalSpace X] [CompactSpace X] : IsCompact (univ : Set X) :=
  isCompact_univ
example {X ι : Type*} [TopologicalSpace X] [CompactSpace X]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i) :
    ∃ t : Finset ι, (univ : Set X) ⊆ ⋃ i ∈ t, U i :=
  isCompact_univ.elim_finite_subcover U hU hcover
example {X : Type*} [TopologicalSpace X] (f : X → X) : ForwardMinimal f ↔
    ∀ x, Dense (range (fun n : ℕ => f^[n] x)) := Iff.rfl
example {X : Type*} [TopologicalSpace X] (f : X → X) (x : X) :
    MultiplyRecurrent f x ↔ ∀ U : Set X, IsOpen U → x ∈ U → ∀ d N : ℕ,
      ∃ n, N ≤ n ∧ 0 < n ∧ ∀ i ≤ d, f^[i*n] x ∈ U := Iff.rfl
example {X : Type*} [TopologicalSpace X] (x : X) (s : Set X) :
    s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t := mem_nhds_iff
example {X : Type*} [TopologicalSpace X] (A : Set X) : A ∈ residual X ↔
    ∃ S : Set (Set X), (∀ U ∈ S, IsOpen U) ∧ (∀ U ∈ S, Dense U) ∧
      S.Countable ∧ ⋂₀ S ⊆ A := mem_residual_iff
example {X : Type*} [TopologicalSpace X] (C : Set X) :
    IsGδ C ↔ ∃ T : Set (Set X), (∀ U ∈ T, IsOpen U) ∧ T.Countable ∧ C = ⋂₀ T := Iff.rfl
example (α : Type*) : Nonempty α ↔ ∃ x : α, x = x := by
  constructor
  · rintro ⟨x⟩; exact ⟨x, rfl⟩
  · rintro ⟨x, _⟩; exact ⟨x⟩
-- END material-imported-definition audit