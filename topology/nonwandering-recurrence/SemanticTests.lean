module
public import RecurrenceSolution
public section
open Set Filter Function TopologicalSpace
-- BEGIN material-imported-definition audit
example {X : Type*} [TopologicalSpace X] (f : X → X) :
    CategoryRecurrence.Nonwandering f ↔ ∀ U : Set X, IsOpen U → U.Nonempty →
      ∃ n : ℕ, 0 < n ∧ ∃ x ∈ U, f^[n] x ∈ U := Iff.rfl
example {X : Type*} [TopologicalSpace X] (f : X → X) (x : X) :
    CategoryRecurrence.Recurrent f x ↔ ∀ U : Set X, IsOpen U → x ∈ U →
      ∀ N : ℕ, ∃ n : ℕ, N < n ∧ f^[n] x ∈ U := Iff.rfl
example (k : ℕ) : CategoryRecurrence.radius k = 1 / ((k : ℝ) + 1) := rfl
example {X : Type*} [MetricSpace X] (f : X → X) (k N : ℕ) (x : X) :
    x ∈ CategoryRecurrence.ReturnStage f k N ↔
      ∃ n : ℕ, N < n ∧ dist (f^[n] x) x < 1 / ((k : ℝ) + 1) := Iff.rfl
example {X : Type*} [TopologicalSpace X] (f : X → X) : f^[0] = id := rfl
example {X : Type*} [TopologicalSpace X] : CategoryRecurrence.Nonwandering (id : X → X) := by
  intro U _hU hnU
  obtain ⟨x, hx⟩ := hnU
  exact ⟨1, by decide, x, hx, by simpa using hx⟩
example {X : Type*} [TopologicalSpace X] (x : X) : CategoryRecurrence.Recurrent id x := by
  intro U _hU hx N
  exact ⟨N + 1, by omega, by simpa using hx⟩
example {X : Type*} [TopologicalSpace X] (U : Set X) : U.Nonempty ↔ ∃ x, x ∈ U := Iff.rfl
example {X : Type*} [TopologicalSpace X] (C : Set X) :
    Dense C ↔ ∀ x, x ∈ closure C := Iff.rfl
example {X : Type*} [TopologicalSpace X] (C : Set X) :
    IsGδ C ↔ ∃ T : Set (Set X), (∀ U ∈ T, IsOpen U) ∧ T.Countable ∧ C = ⋂₀ T := Iff.rfl
example {X : Type*} [TopologicalSpace X] (A : Set X) : A ∈ residual X ↔
    ∃ S : Set (Set X), (∀ U ∈ S, IsOpen U) ∧ (∀ U ∈ S, Dense U) ∧
      S.Countable ∧ ⋂₀ S ⊆ A := mem_residual_iff
example {X : Type*} [TopologicalSpace X] [BaireSpace X] {A : Set X}
    (h : A ∈ residual X) : Dense A := dense_of_mem_residual h
example {X : Type*} [MetricSpace X] (x y : X) (r : ℝ) :
    y ∈ Metric.ball x r ↔ dist y x < r := Iff.rfl
example {X : Type*} [MetricSpace X] (x y z : X) :
    dist x x = 0 ∧ dist x y = dist y x ∧ dist x z ≤ dist x y + dist y z :=
  ⟨dist_self x, dist_comm x y, dist_triangle x y z⟩
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := continuous_def
example (N n : ℕ) (h : N < n) : 0 < n := by omega
example (N n : ℕ) : N < n ↔ Nat.succ N ≤ n := Iff.rfl
-- END material-imported-definition audit
