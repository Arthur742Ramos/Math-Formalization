module
public import Solution
-- BEGIN material-imported-definition audit
namespace ComputationalHodge.GeometricDescent.Semantics
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.PresentationHomology
open scoped InnerProductSpace
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [Fintype E] [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E}

example {a b : A} (p q : GeometricTrace S.toGeometricStepSystem a b) :
    (geometricPresentation S).rule p q ↔
      _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q) := Iff.rfl
example (l : NullLoop S) :
    _root_.Path.Homotopic (GeometricTrace.realize l.val.2) (_root_.Path.refl l.val.1) := l.property
example {a b : A} (p : GeometricTrace S.toGeometricStepSystem a b) :
    realization (geometricPresentation S) (Quotient.mk _ p) =
      _root_.Path.Homotopic.Quotient.mk (GeometricTrace.realize p) := rfl
example {a b : A} (p : PathClass (geometricPresentation S) a b) :
    (representedEquiv (S := S)).symm (representedEquiv p) = p :=
  (representedEquiv (S := S)).left_inv p
example {a b : A} (x : RealizedArrow S a b) :
    representedEquiv ((representedEquiv (S := S)).symm x) = x :=
  (representedEquiv (S := S)).right_inv x

example : NullSpan S = Submodule.span ℝ (Set.range (fun l : NullLoop S => wordChain l.val.2)) := rfl
example (ω : Cochain E) : GeometricInvariant (S := S) ω ↔
    ∀ {a b : A} (p q : GeometricTrace S.toGeometricStepSystem a b),
      _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q) → period p ω = period q ω := Iff.rfl
example (P : ScopedGeometricRewritePresentation S) (z : Cochain E) :
    z ∈ Relations P ↔ ∃ c : Cell P →₀ ℝ, boundary₂ P c = z := Iff.rfl
example (P : ScopedGeometricRewritePresentation S) (c : Cell P →₀ ℝ) :
    boundary₂ P c = c.sum (fun x r => r • (wordChain x.left - wordChain x.right)) := rfl
example (f : A → ℝ) (c : A →₀ ℝ) : vertexEval f c = c.sum (fun a r => r • f a) := rfl
example (e : E) : boundary₁ S.toGeometricStepSystem (EuclideanSpace.basisFun E ℝ e) =
    Finsupp.single (S.tgt e) 1 - Finsupp.single (S.src e) 1 :=
  (EuclideanSpace.basisFun E ℝ).toBasis.constr_basis ℝ _ e
example (L : Submodule ℝ (Cochain E)) (f : Cochain E →ₗ[ℝ] Cochain E) (z : Cochain E) :
    z ∈ L.map f ↔ ∃ x, x ∈ L ∧ f x = z := Iff.rfl
example (P : ScopedGeometricRewritePresentation S) :
    ChainH1 P = (Cycles S.toGeometricStepSystem ⧸ ChainBoundaries P) := rfl
example (P : ScopedGeometricRewritePresentation S) (z w : Cycles S.toGeometricStepSystem) :
    (ChainBoundaries P).mkQ z = (ChainBoundaries P).mkQ w ↔ z - w ∈ ChainBoundaries P :=
  Submodule.Quotient.eq (ChainBoundaries P)
example (P : ScopedGeometricRewritePresentation S) (ω : Closed P) :
    (Boundaries P).mkQ ω = 0 ↔ (ω : Cochain E) ∈ Exact S :=
  Submodule.Quotient.mk_eq_zero (Boundaries P)
example (P : ScopedGeometricRewritePresentation S) (z : Cycles S.toGeometricStepSystem) :
    homologyMap P ((ChainBoundaries P).mkQ z) =
      (ChainBoundaries (geometricPresentation S)).mkQ z := rfl
example (P : ScopedGeometricRewritePresentation S) (ω : Closed (geometricPresentation S)) :
    cohomologyMap P ((Boundaries (geometricPresentation S)).mkQ ω) =
      (Boundaries P).mkQ ⟨ω,geometric_closed_le P ω.property⟩ := rfl
example (P : ScopedGeometricRewritePresentation S) :
    Module.Dual ℝ (ChainH1 P) = (ChainH1 P →ₗ[ℝ] ℝ) := rfl
example (P : ScopedGeometricRewritePresentation S) (c : H1 (geometricPresentation S)) (z : ChainH1 P) :
    pairing P (cohomologyMap P c) z = pairing (geometricPresentation S) c (homologyMap P z) :=
  pairing_compatibility P c z
example (P : ScopedGeometricRewritePresentation S) :
    Function.Surjective (homologyMap P) := homologyMap_surjective P
example (P : ScopedGeometricRewritePresentation S) :
    Function.Injective (cohomologyMap P) := cohomologyMap_injective P
example (P : ScopedGeometricRewritePresentation S) : FiniteDimensional ℝ (ChainH1 P) := inferInstance
example (P : ScopedGeometricRewritePresentation S) (ω : Cochain E) :
    ω ∈ Harmonic P ↔ ω ∈ Closed P ∧ ω ∈ (Exact S)ᗮ := Iff.rfl
end ComputationalHodge.GeometricDescent.Semantics
-- END material-imported-definition audit
