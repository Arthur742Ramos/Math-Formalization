module
public import LESolution
@[expose] public section
noncomputable section
open Set Function Filter Topology TopologicalSpace
open scoped Uniformity
open Lavrentieff
-- BEGIN material-imported-definition audit
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [IsCompletelyMetrizableSpace X] [IsCompletelyMetrizableSpace Y]
    {s : Set X} {t : Set Y} (h : s ≃ₜ t) :
    ∃ (B : Set X) (C : Set Y) (hsB : s ⊆ B),
      IsGδ B ∧ IsGδ C ∧ t ⊆ C ∧ B ⊆ closure s ∧ C ⊆ closure t ∧
      ∃ H : B ≃ₜ C, ∀ x : s, (H ⟨x, hsB x.property⟩ : Y) = (h x : Y) :=
  completely_metrizable_extension h
example {X : Type*} [TopologicalSpace X] (s : Set X) :
    IsGδ s ↔ ∃ U : ℕ → Set X, (∀ n, IsOpen (U n)) ∧ s = ⋂ n, U n :=
  isGδ_iff_eq_iInter_nat
example {X : Type*} [TopologicalSpace X] (s : Set X) (x : X) :
    x ∈ closure s ↔ ∀ U ∈ 𝓝 x, (U ∩ s).Nonempty := mem_closure_iff_nhds
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) :
    Bijective h ∧ Continuous h ∧ Continuous h.symm := ⟨h.bijective, h.continuous, h.symm.continuous⟩
example {X : Type*} [t : TopologicalSpace X] (s : Set X) :
    (inferInstance : TopologicalSpace s) = TopologicalSpace.induced ((↑) : s → X) t := rfl
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (s : Set X) :
    ContinuousOn f s ↔ ∀ x ∈ s, Tendsto f (𝓝[s] x) (𝓝 (f x)) := Iff.rfl
example {X : Type*} [TopologicalSpace X] (s : Set X) (x : X) :
    𝓝[s] x = 𝓝 x ⊓ 𝓟 s := rfl
example {X : Type*} [UniformSpace X] :
    CompleteSpace X ↔ ∀ f : Filter X, Cauchy f → ∃ x, f ≤ 𝓝 x := by
  constructor
  · intro h f hf; exact h.complete hf
  · intro h; exact ⟨fun {f} hf => h f hf⟩
example {X : Type*} [UniformSpace X] (f : Filter X) :
    Cauchy f ↔ f.NeBot ∧ f ×ˢ f ≤ 𝓤 X := Iff.rfl
example {X : Type*} [t : TopologicalSpace X] [h : IsCompletelyMetrizableSpace X] :
    ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧
      @CompleteSpace X m.toUniformSpace := h.complete
example {X Y : Type*} (f : X → Y) (g : Y → X) (s : Set X) (t : Set Y) :
    (MapsTo f s t ↔ ∀ x ∈ s, f x ∈ t) ∧
    (LeftInvOn g f s ↔ ∀ x ∈ s, g (f x) = x) ∧
    (EqOn (g ∘ f) id s ↔ ∀ x ∈ s, g (f x) = x) := ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (s : Set X) (f : X → Y) :
    extensionDomain s f = closure s ∩ ⋂ n : ℕ, smallOscillation s f ((n + 1 : ℝ)⁻¹) := rfl
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (s : Set X) (f : X → Y) (ε : ℝ) (x : X) :
    x ∈ smallOscillation s f ε ↔ ∃ U, IsOpen U ∧ x ∈ U ∧
      ∀ a ∈ U ∩ s, ∀ b ∈ U ∩ s, dist (f a) (f b) < ε := mem_smallOscillation_iff
-- Empty ambient types and empty subsets are admitted, without extra inhabitants.
example : ∃ (B C : Set Empty) (hsB : (∅ : Set Empty) ⊆ B),
    IsGδ B ∧ IsGδ C ∧ (∅ : Set Empty) ⊆ C ∧ B ⊆ closure ∅ ∧ C ⊆ closure ∅ ∧
    ∃ H : B ≃ₜ C, ∀ x : (∅ : Set Empty),
      (H ⟨x, hsB x.property⟩ : Empty) = ((Homeomorph.refl (∅ : Set Empty)) x : Empty) :=
  homeomorph_extension (Homeomorph.refl (∅ : Set Empty))
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    extensionDomain ∅ f = ∅ := by simp [extensionDomain]
-- The closure condition is substantive: for an empty source no extra point is admitted.
example {X : Type*} [TopologicalSpace X] {B : Set X} (h : B ⊆ closure (∅ : Set X)) :
    B = ∅ := by simpa using h
-- END material-imported-definition audit
