module
public import Homology
public import Mathlib.LinearAlgebra.Dual.Lemmas
@[expose] public section
namespace ComputationalHodge.PresentationHomology
open ComputationalPaths.Path.GeometricTopology
open scoped InnerProductSpace
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [Fintype E] [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E}

noncomputable def cycleEvaluation (P : ScopedGeometricRewritePresentation S) (ω : Closed P) :
    Module.Dual ℝ (ChainH1 P) :=
  (ChainBoundaries P).liftQ
    ((innerSL ℝ (ω : Cochain E)).toLinearMap.comp (Cycles S.toGeometricStepSystem).subtype) (by
      intro z hz
      have hc : (ω : Cochain E) ∈ (Relations P)ᗮ := by
        rw [← closed_eq_relations_orthogonal]; exact ω.property
      exact Submodule.inner_left_of_mem_orthogonal
        (show (z : Cochain E) ∈ Relations P from hz) hc)

noncomputable def evaluationMap (P : ScopedGeometricRewritePresentation S) :
    Closed P →ₗ[ℝ] Module.Dual ℝ (ChainH1 P) where
  toFun := cycleEvaluation P
  map_add' ω η := by
    apply LinearMap.ext; intro z
    induction z using Submodule.Quotient.induction_on with | _ z =>
    change inner ℝ ((ω : Cochain E) + η) z =
      inner ℝ (ω : Cochain E) (z : Cochain E) + inner ℝ (η : Cochain E) (z : Cochain E)
    exact inner_add_left _ _ _
  map_smul' r ω := by
    apply LinearMap.ext; intro z
    induction z using Submodule.Quotient.induction_on with | _ z =>
    change inner ℝ (r • (ω : Cochain E)) z = r * inner ℝ (ω : Cochain E) (z : Cochain E)
    exact real_inner_smul_left _ _ r

noncomputable def pairing (P : ScopedGeometricRewritePresentation S) :
    H1 P →ₗ[ℝ] Module.Dual ℝ (ChainH1 P) :=
  (Boundaries P).liftQ (evaluationMap P) (by
    intro ω hω
    apply LinearMap.ext; intro z
    induction z using Submodule.Quotient.induction_on with | _ z =>
    change inner ℝ (ω : Cochain E) z = 0
    have hz : (z : Cochain E) ∈ (Exact S)ᗮ := by
      rw [← cycles_eq_exact_orthogonal]; exact z.property
    exact Submodule.inner_right_of_mem_orthogonal
      (show (ω : Cochain E) ∈ Exact S from hω) hz)

theorem pairing_mk (P : ScopedGeometricRewritePresentation S) (ω : Closed P)
    (z : Cycles S.toGeometricStepSystem) :
    pairing P ((Boundaries P).mkQ ω) ((ChainBoundaries P).mkQ z) = inner ℝ (ω : Cochain E) z := rfl

theorem pairing_loopClass (P : ScopedGeometricRewritePresentation S) {a : A}
    (p : PathClass P a a) (c : H1 P) : pairing P c (loopClass P a p) = periodPairing P a p c := by
  induction p using Quotient.inductionOn with | _ p =>
  induction c using Submodule.Quotient.induction_on with | _ ω =>
  change inner ℝ (ω : Cochain E) (wordChain p) = period p ω
  rw [real_inner_comm, wordChain_period]

end ComputationalHodge.PresentationHomology
