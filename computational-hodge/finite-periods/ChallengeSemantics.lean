module

public import Challenge

@[expose] public section
namespace BridgeSemantics
open ComputationalHodge ComputationalPaths.Path.GeometricTopology
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [Fintype E] [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E} (P : ScopedGeometricRewritePresentation S)

-- BEGIN material-imported-definition audit
example (ω : Cochain E) : ω ∈ Closed P ↔ d1 P ω = 0 := Iff.rfl
example (ω : Cochain E) : ω ∈ Exact S ↔ ∃ f, d0 S.toGeometricStepSystem f = ω := Iff.rfl
example (ω : Cochain E) :
    ω ∈ Harmonic P ↔ ω ∈ Closed P ∧ ω ∈ (Exact S)ᗮ := Iff.rfl
example (ω : Closed P) :
    (harmonicProjection P ω : Cochain E) = (ω : Cochain E) - (Exact S).starProjection ω := rfl
example (ω η : Closed P) :
    (Boundaries P).mkQ ω = (Boundaries P).mkQ η ↔
      (ω : Cochain E) - (η : Cochain E) ∈ Exact S :=
  Submodule.Quotient.eq (Boundaries P)
example (e : E) (ω : Cochain E) : period (GeometricTrace.single (S := S.toGeometricStepSystem) e) ω = ω e := rfl
example (f : A → ℝ) (e : E) :
    d0 S.toGeometricStepSystem f e = f (S.tgt e) - f (S.src e) := rfl
example (ω : Cochain E) (c : Cell P) : d1 P ω c = period c.left ω - period c.right ω := rfl
example (ω η : Cochain E) : inner ℝ ω η = ∑ e, ω e * η e := by
  simp [PiLp.inner_apply, mul_comm]
example (ω : Cochain E) : (WithLp.linearEquiv 2 ℝ (E → ℝ)) ω = ω.ofLp := rfl
example : FiniteDimensional ℝ (Exact S) := inferInstance
example : CompleteSpace (Exact S) := inferInstance
example : (Exact S).HasOrthogonalProjection := inferInstance
example (ω : Cochain E) : (Exact S).starProjection ω ∈ Exact S :=
  (Exact S).starProjection_apply_mem ω
example (ω : Cochain E) : ω - (Exact S).starProjection ω ∈ (Exact S)ᗮ :=
  (Exact S).sub_starProjection_mem_orthogonal ω
example (a : A) : Nonempty (GeometricTrace S.toGeometricStepSystem
    (componentRoot S.toGeometricStepSystem a) a) := ⟨rootTrace S.toGeometricStepSystem a⟩
example (f : A → ℝ) {a b : A} (p : GeometricTrace S.toGeometricStepSystem a b) :
    period p (d0 S.toGeometricStepSystem f) = f b - f a := period_d0 f p
example {a : A} (p : GeometricTrace S.toGeometricStepSystem a a) (ω : Closed P) :
    periodPairing P a (Quotient.mk _ p) ((Boundaries P).mkQ ω) = period p ω := rfl
example (ω : Closed P) :
    hodgeEquiv P ((Boundaries P).mkQ ω) = harmonicProjection P ω := hodgeEquiv_mk P ω
-- END material-imported-definition audit

end BridgeSemantics
