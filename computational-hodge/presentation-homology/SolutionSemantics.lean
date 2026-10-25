module
public import Solution
-- BEGIN material-imported-definition audit
namespace ComputationalHodge.PresentationHomology.Semantics
open ComputationalPaths.Path.GeometricTopology
open scoped InnerProductSpace
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [Fintype E] [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E}

-- Actual finitely supported algebraic evaluation, with no continuity premise.
example (f : A → ℝ) (c : A →₀ ℝ) : vertexEval f c = c.sum (fun a r => r • f a) := rfl
example (f : A → ℝ) (c : A →₀ ℝ) :
    c.sum (fun a r => r • f a) = ∑ a ∈ c.support, c a • f a := rfl
example (e : E) : boundary₁ S.toGeometricStepSystem (EuclideanSpace.basisFun E ℝ e) =
    Finsupp.single (S.tgt e) 1 - Finsupp.single (S.src e) 1 :=
  (EuclideanSpace.basisFun E ℝ).toBasis.constr_basis ℝ _ e
example (P : ScopedGeometricRewritePresentation S) (c : Cell P →₀ ℝ) :
    boundary₂ P c = c.sum (fun x r => r • (wordChain x.left - wordChain x.right)) := rfl
example (P : ScopedGeometricRewritePresentation S) :
    Relations P = Submodule.span ℝ
      (Set.range fun c : Cell P => wordChain c.left - wordChain c.right) := relations_eq_span P
example : Cycles S.toGeometricStepSystem = LinearMap.ker (boundary₁ S.toGeometricStepSystem) := rfl
example (P : ScopedGeometricRewritePresentation S) : Relations P = LinearMap.range (boundary₂ P) := rfl
example (P : ScopedGeometricRewritePresentation S) :
    ChainBoundaries P = (Relations P).comap (Cycles S.toGeometricStepSystem).subtype := rfl
example (P : ScopedGeometricRewritePresentation S) :
    ChainH1 P = (Cycles S.toGeometricStepSystem ⧸ ChainBoundaries P) := rfl
example (P : ScopedGeometricRewritePresentation S) :
    Module.Dual ℝ (ChainH1 P) = (ChainH1 P →ₗ[ℝ] ℝ) := rfl
example (P : ScopedGeometricRewritePresentation S) : FiniteDimensional ℝ (ChainH1 P) := inferInstance
example (P : ScopedGeometricRewritePresentation S) :
    FiniteDimensional ℝ (Module.Dual ℝ (ChainH1 P)) := inferInstance
example (P : ScopedGeometricRewritePresentation S) : CompleteSpace (Relations P) := inferInstance
example (P : ScopedGeometricRewritePresentation S) :
    (Relations P).HasOrthogonalProjection := inferInstance
example (P : ScopedGeometricRewritePresentation S) (z : Cycles S.toGeometricStepSystem) :
    (chainHarmonicProjection P z : Cochain E) = (z : Cochain E) - (Relations P).starProjection z := rfl
example (P : ScopedGeometricRewritePresentation S) :
    (periodDuality P).toLinearMap = pairing P := rfl
example (P : ScopedGeometricRewritePresentation S) (φ : Module.Dual ℝ (ChainH1 P)) :
    ∃ c : H1 P, pairing P c = φ := (periodDuality P).surjective φ
example (P : ScopedGeometricRewritePresentation S) (z w : Cycles S.toGeometricStepSystem) :
    (ChainBoundaries P).mkQ z = (ChainBoundaries P).mkQ w ↔ z - w ∈ ChainBoundaries P :=
  Submodule.Quotient.eq (ChainBoundaries P)
example (P : ScopedGeometricRewritePresentation S) (ω : Closed P)
    (z : Cycles S.toGeometricStepSystem) :
    periodDuality P ((Boundaries P).mkQ ω) ((ChainBoundaries P).mkQ z) =
      inner ℝ (ω : Cochain E) (z : Cochain E) := periodDuality_mk P ω z
end ComputationalHodge.PresentationHomology.Semantics
-- END material-imported-definition audit
