module
public import Challenge
-- BEGIN material-imported-definition audit
namespace ComputationalHodge.GeometricObstruction.Semantics
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.PresentationHomology ComputationalHodge.GeometricDescent
open scoped InnerProductSpace
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [Fintype E] [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E}

example {a b : A} (p q : GeometricTrace S.toGeometricStepSystem a b) :
    (geometricPresentation S).rule p q ↔
      _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q) := Iff.rfl
example (l : NullLoop S) :
    _root_.Path.Homotopic (GeometricTrace.realize l.val.2) (_root_.Path.refl l.val.1) := l.property
example : NullSpan S = Submodule.span ℝ (Set.range (fun l : NullLoop S => wordChain l.val.2)) := rfl
example (P : ScopedGeometricRewritePresentation S) (ω : Cochain E) :
    ω ∈ Obstruction P ↔ ω ∈ NullSpan S ∧ ω ∈ (Relations P)ᗮ := Iff.rfl
example (P : ScopedGeometricRewritePresentation S) (ω : Cochain E) :
    ω ∈ Harmonic P ↔ ω ∈ Closed P ∧ ω ∈ (Exact S)ᗮ := Iff.rfl
example (P : ScopedGeometricRewritePresentation S) (z : Cochain E) :
    z ∈ Relations P ↔ ∃ c : Cell P →₀ ℝ, boundary₂ P c = z := Iff.rfl
example (P : ScopedGeometricRewritePresentation S) (c : Cell P →₀ ℝ) :
    boundary₂ P c = c.sum (fun x r => r • (wordChain x.left - wordChain x.right)) := rfl
example (e : E) : boundary₁ S.toGeometricStepSystem (EuclideanSpace.basisFun E ℝ e) =
    Finsupp.single (S.tgt e) 1 - Finsupp.single (S.src e) 1 :=
  (EuclideanSpace.basisFun E ℝ).toBasis.constr_basis ℝ _ e
example (P : ScopedGeometricRewritePresentation S) :
    ChainH1 P = (Cycles S.toGeometricStepSystem ⧸ ChainBoundaries P) := rfl
example (P : ScopedGeometricRewritePresentation S) (z w : Cycles S.toGeometricStepSystem) :
    (ChainBoundaries P).mkQ z = (ChainBoundaries P).mkQ w ↔ z - w ∈ ChainBoundaries P :=
  Submodule.Quotient.eq (ChainBoundaries P)
example (P : ScopedGeometricRewritePresentation S) (z : Cycles S.toGeometricStepSystem) :
    ‖(ChainBoundaries P).mkQ z‖ =
      sInf ((fun w : Cycles S.toGeometricStepSystem => ‖z + w‖) ''
        ((ChainBoundaries P).toAddSubgroup : Set (Cycles S.toGeometricStepSystem))) :=
  quotient_norm_mk_eq (ChainBoundaries P).toAddSubgroup z
example (P : ScopedGeometricRewritePresentation S) (z : Cycles S.toGeometricStepSystem)
    (hz : z ∈ (ChainBoundaries P)ᗮ) :
    (ChainBoundaries P).quotientEquivOrthogonal (Submodule.Quotient.mk z) = ⟨z,hz⟩ :=
  (ChainBoundaries P).quotientEquivOrthogonal_mk z hz
example (P : ScopedGeometricRewritePresentation S) (b : Obstruction P) :
    ‖(obstructionKernelEquiv P b).val‖ = ‖(b : Cochain E)‖ := obstructionToKernel_norm P b
example (P : ScopedGeometricRewritePresentation S) (b : Obstruction P) :
    (obstructionKernelEquiv P).symm (obstructionKernelEquiv P b) = b :=
  (obstructionKernelEquiv P).left_inv b
example (P : ScopedGeometricRewritePresentation S) (q : LinearMap.ker (homologyMap P)) :
    obstructionKernelEquiv P ((obstructionKernelEquiv P).symm q) = q :=
  (obstructionKernelEquiv P).right_inv q
example (P : ScopedGeometricRewritePresentation S) (h : Harmonic P) :
    (geometricCorrection P h : Cochain E) = (h : Cochain E) - (NullSpan S).starProjection h := rfl
example (P : ScopedGeometricRewritePresentation S) (h : Harmonic P) :
    (obstructionProjection P h : Cochain E) = (NullSpan S).starProjection h := rfl
example (ω : Cochain E) : ‖ω‖ ^ 2 = inner ℝ ω ω := (real_inner_self_eq_norm_sq ω).symm
example (P : ScopedGeometricRewritePresentation S) : FiniteDimensional ℝ (ChainH1 P) := inferInstance
example (ω : Cochain E) :
    GeometricInvariant (S := S) ω ↔ ∀ {a b : A} (p q : GeometricTrace S.toGeometricStepSystem a b),
      _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q) → period p ω = period q ω := Iff.rfl
end ComputationalHodge.GeometricObstruction.Semantics
-- END material-imported-definition audit
