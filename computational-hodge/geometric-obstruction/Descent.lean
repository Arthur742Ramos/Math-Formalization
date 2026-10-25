module
public import Realization
@[expose] public section
namespace ComputationalHodge.GeometricDescent
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.PresentationHomology
open scoped InnerProductSpace
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [Fintype E] [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E}


theorem chainBoundaries_le (P : ScopedGeometricRewritePresentation S) :
    ChainBoundaries P ≤ ChainBoundaries (geometricPresentation S) := by
  intro z hz
  change (z : Cochain E) ∈ Relations (geometricPresentation S)
  rw [geometric_relations_eq_nullSpan]
  exact presentation_relations_le_nullSpan P hz

noncomputable def homologyMap (P : ScopedGeometricRewritePresentation S) :
    ChainH1 P →ₗ[ℝ] ChainH1 (geometricPresentation S) :=
  (ChainBoundaries P).liftQ (ChainBoundaries (geometricPresentation S)).mkQ
    (by simpa only [Submodule.ker_mkQ] using chainBoundaries_le P)

theorem homologyMap_mk (P : ScopedGeometricRewritePresentation S)
    (z : Cycles S.toGeometricStepSystem) :
    homologyMap P ((ChainBoundaries P).mkQ z) =
      (ChainBoundaries (geometricPresentation S)).mkQ z := rfl


theorem geometric_closed_iff_null_periods (ω : Cochain E) :
    ω ∈ Closed (geometricPresentation S) ↔ ∀ l : NullLoop S, period l.val.2 ω = 0 := by
  rw [closed_eq_relations_orthogonal,geometric_relations_eq_nullSpan]
  constructor
  · intro h l
    exact (wordChain_period l.val.2 ω).symm.trans (h _ (Submodule.subset_span ⟨l,rfl⟩))
  · intro h
    have hz : NullSpan S ≤ LinearMap.ker (innerSL ℝ ω).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨l,rfl⟩
      change inner ℝ ω (wordChain l.val.2) = 0
      rw [real_inner_comm,wordChain_period,h l]
    intro z hz'
    exact (real_inner_comm _ _).trans (hz hz')

def GeometricInvariant (ω : Cochain E) : Prop :=
  ∀ {a b : A} (p q : GeometricTrace S.toGeometricStepSystem a b),
    _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q) → period p ω = period q ω

theorem period_descent_iff (ω : Cochain E) :
    GeometricInvariant (S := S) ω ↔ ∀ l : NullLoop S, period l.val.2 ω = 0 := by
  constructor
  · intro h l
    exact (h l.val.2 (.refl l.val.1) l.property).trans rfl
  · intro h a b p q hpq
    exact period_rewrite (geometricPresentation S)
      ⟨ω,(geometric_closed_iff_null_periods ω).mpr h⟩ (.generator hpq)

theorem geometric_closed_le (P : ScopedGeometricRewritePresentation S) :
    Closed (geometricPresentation S) ≤ Closed P := by
  rw [closed_eq_relations_orthogonal,closed_eq_relations_orthogonal]
  intro ω h z hz
  exact h z (by rw [geometric_relations_eq_nullSpan]; exact presentation_relations_le_nullSpan P hz)


theorem harmonic_descent_iff (P : ScopedGeometricRewritePresentation S) (h : Harmonic P) :
    (h : Cochain E) ∈ Harmonic (geometricPresentation S) ↔
      ∀ l : NullLoop S, period l.val.2 h = 0 := by
  constructor
  · intro hg
    exact (geometric_closed_iff_null_periods _).mp hg.1
  · intro hn
    exact ⟨(geometric_closed_iff_null_periods _).mpr hn,h.property.2⟩

end ComputationalHodge.GeometricDescent
