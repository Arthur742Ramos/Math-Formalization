module

public import Periods
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section
namespace ComputationalHodge
open ComputationalPaths.Path.GeometricTopology
open scoped InnerProductSpace
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [Fintype E] [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E}

noncomputable def Harmonic (P : ScopedGeometricRewritePresentation S) : Submodule ℝ (Cochain E) :=
  Closed P ⊓ (Exact S)ᗮ

/-- Boundaries as a subspace of cycles, rather than an ill-typed ambient quotient. -/
def Boundaries (P : ScopedGeometricRewritePresentation S) : Submodule ℝ (Closed P) :=
  (Exact S).comap (Closed P).subtype

abbrev H1 (P : ScopedGeometricRewritePresentation S) := Closed P ⧸ Boundaries P

def cohomologyPeriod (P : ScopedGeometricRewritePresentation S) {a : A}
    (p : GeometricTrace S.toGeometricStepSystem a a) : H1 P →ₗ[ℝ] ℝ :=
  (Boundaries P).liftQ ((period p).comp (Closed P).subtype) (by
    rintro ω ⟨f, hf⟩
    change d0 S.toGeometricStepSystem f = (ω : Cochain E) at hf
    change period p (ω : Cochain E) = 0
    rw [← hf, period_d0, sub_self])

theorem cohomologyPeriod_mk (P : ScopedGeometricRewritePresentation S) {a : A}
    (p : GeometricTrace S.toGeometricStepSystem a a) (ω : Closed P) :
    cohomologyPeriod P p ((Boundaries P).mkQ ω) = period p ω := rfl

/-- A period pairing with both the actual scoped path quotient and actual H1. -/
def periodPairing (P : ScopedGeometricRewritePresentation S) (a : A) :
    PathClass P a a → H1 P →ₗ[ℝ] ℝ :=
  Quotient.lift (cohomologyPeriod P) (by
    intro p q hpq
    apply LinearMap.ext
    intro c
    induction c using Submodule.Quotient.induction_on with
    | _ ω => exact period_rewrite P ω hpq)

end ComputationalHodge
