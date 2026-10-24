module
public import DichotomySolution
public section
open Set Function Metric
-- BEGIN material-imported-definition audit
example {X : Type*} [TopologicalSpace X] (f : X → X) :
    AuslanderYorke.Minimal f ↔ ∀ x, Dense (range (fun n : ℕ => f^[n] x)) := Iff.rfl
example {X : Type*} [MetricSpace X] (f : X → X) :
    AuslanderYorke.Sensitive f ↔ ∃ δ : ℝ, 0 < δ ∧ ∀ U : Set X, IsOpen U → U.Nonempty →
      ∃ n : ℕ, ∃ a ∈ U, ∃ b ∈ U, δ < dist (f^[n] a) (f^[n] b) := Iff.rfl
example {X : Type*} [MetricSpace X] [IsEmpty X] (f : X → X) :
    AuslanderYorke.Sensitive f := by
  refine ⟨1, by norm_num, ?_⟩
  intro U _ hU
  obtain ⟨x, _⟩ := hU
  exact isEmptyElim x
example {X : Type*} [MetricSpace X] [IsEmpty X] (f : X → X) :
    Equicontinuous (fun n : ℕ => f^[n]) := fun x => isEmptyElim x
example {X : Type*} [TopologicalSpace X] (s : Set X) :
    Dense s ↔ ∀ U, IsOpen U → U.Nonempty → (U ∩ s).Nonempty := dense_iff_inter_open
example {X : Type*} [TopologicalSpace X] (s : Set X) : Dense s ↔ ∀ x, x ∈ closure s := Iff.rfl
example {X : Type*} [TopologicalSpace X] (s : Set X) : IsClosed s ↔ IsOpen sᶜ := ⟨fun h => h.isOpen_compl, fun h => ⟨h⟩⟩
example {X : Type*} [TopologicalSpace X] (s : Set X) (x : X) :
    x ∈ closure s ↔ ∀ U, IsOpen U → x ∈ U → (U ∩ s).Nonempty := mem_closure_iff
example {X Y : Type*} (g : X → Y) (y : Y) : y ∈ range g ↔ ∃ x, g x = y := Iff.rfl
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := continuous_def
example {X : Type*} : Nonempty X ↔ ∃ _x : X, True :=
  ⟨fun ⟨x⟩ => ⟨x, trivial⟩, fun ⟨x, _⟩ => ⟨x⟩⟩
example {X : Type*} (f : X → X) (x : X) : f^[0] x = x := rfl
example {X : Type*} (f : X → X) (n : ℕ) (x : X) : f^[n+1] x = f^[n] (f x) := rfl
example {X : Type*} [MetricSpace X] (f : X → X) :
    Equicontinuous (fun n : ℕ => f^[n]) ↔ ∀ x, EquicontinuousAt (fun n : ℕ => f^[n]) x := Iff.rfl
example {X : Type*} [MetricSpace X] (f : X → X) (x : X) :
    EquicontinuousAt (fun n : ℕ => f^[n]) x ↔ ∀ ε > 0, ∃ δ > 0,
      ∀ y, dist y x < δ → ∀ n : ℕ, dist (f^[n] x) (f^[n] y) < ε := Metric.equicontinuousAt_iff
example {X : Type*} [MetricSpace X] (x y : X) (ε : ℝ) : y ∈ ball x ε ↔ dist y x < ε := Iff.rfl
example {X : Type*} [MetricSpace X] (x y z : X) : dist x z ≤ dist x y + dist y z := dist_triangle x y z
example {X ι : Type*} [t : TopologicalSpace X] :
    (inferInstance : TopologicalSpace (ι → X)) =
      ⨅ i : ι, TopologicalSpace.induced (fun x : ι → X => x i) t := rfl
example {ι : Type*} (s : Finset ι) : (s : Set ι).Finite := s.finite_toSet
-- END material-imported-definition audit
