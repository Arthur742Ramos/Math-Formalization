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

theorem geometric_chainBoundaries_eq : ChainBoundaries (geometricPresentation S) =
    Submodule.span ℝ (Set.range (fun l : NullLoop S => loopCycle l.val.2)) := by
  have hm : (Submodule.span ℝ (Set.range (fun l : NullLoop S => loopCycle l.val.2))).map
      (Cycles S.toGeometricStepSystem).subtype = NullSpan S := by
    rw [Submodule.map_span]
    rw [← Set.range_comp]
    rfl
  ext z
  change (z : Cochain E) ∈ Relations (geometricPresentation S) ↔ _
  rw [geometric_relations_eq_nullSpan,← hm]
  constructor
  · rintro ⟨w,hw,heq⟩
    exact (Subtype.ext heq : w = z) ▸ hw
  · intro hz
    exact ⟨z,hz,rfl⟩

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

theorem homologyMap_surjective (P : ScopedGeometricRewritePresentation S) :
    Function.Surjective (homologyMap P) := by
  intro c
  induction c using Submodule.Quotient.induction_on with | _ z =>
  exact ⟨(ChainBoundaries P).mkQ z,rfl⟩

noncomputable def NullClassSpan (P : ScopedGeometricRewritePresentation S) :
    Submodule ℝ (ChainH1 P) :=
  Submodule.span ℝ (Set.range (fun l : NullLoop S =>
    loopClass P l.val.1 (Quotient.mk _ l.val.2)))

theorem homologyMap_kernel (P : ScopedGeometricRewritePresentation S) :
    LinearMap.ker (homologyMap P) = NullClassSpan P := by
  rw [homologyMap,Submodule.ker_liftQ,Submodule.ker_mkQ,geometric_chainBoundaries_eq,
    Submodule.map_span]
  rw [← Set.range_comp]
  rfl

theorem homologyMap_nullLoop (P : ScopedGeometricRewritePresentation S) (l : NullLoop S) :
    homologyMap P (loopClass P l.val.1 (Quotient.mk _ l.val.2)) = 0 := by
  apply (show loopClass P l.val.1 (Quotient.mk _ l.val.2) ∈ LinearMap.ker (homologyMap P) ↔ _ from Iff.rfl).mp
  rw [homologyMap_kernel]
  exact Submodule.subset_span ⟨l,rfl⟩

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

noncomputable def closedInclusion (P : ScopedGeometricRewritePresentation S) :
    Closed (geometricPresentation S) →ₗ[ℝ] Closed P := Submodule.inclusion (geometric_closed_le P)

noncomputable def cohomologyMap (P : ScopedGeometricRewritePresentation S) :
    H1 (geometricPresentation S) →ₗ[ℝ] H1 P :=
  (Boundaries (geometricPresentation S)).liftQ ((Boundaries P).mkQ.comp (closedInclusion P)) (by
    intro ω hω
    change (Boundaries P).mkQ (closedInclusion P ω) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hω)

theorem cohomologyMap_mk (P : ScopedGeometricRewritePresentation S)
    (ω : Closed (geometricPresentation S)) :
    cohomologyMap P ((Boundaries (geometricPresentation S)).mkQ ω) =
      (Boundaries P).mkQ (closedInclusion P ω) := rfl

theorem cohomologyMap_injective (P : ScopedGeometricRewritePresentation S) :
    Function.Injective (cohomologyMap P) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro c hc
  change c = 0
  induction c using Submodule.Quotient.induction_on with | _ ω =>
  change (Boundaries P).mkQ (closedInclusion P ω) = 0 at hc
  have hx := (Submodule.Quotient.mk_eq_zero (Boundaries P)).mp hc
  apply (Submodule.Quotient.mk_eq_zero (Boundaries (geometricPresentation S))).mpr
  change (ω : Cochain E) ∈ Exact S at hx ⊢
  exact hx

theorem pairing_compatibility (P : ScopedGeometricRewritePresentation S)
    (c : H1 (geometricPresentation S)) (z : ChainH1 P) :
    pairing P (cohomologyMap P c) z = pairing (geometricPresentation S) c (homologyMap P z) := by
  induction c using Submodule.Quotient.induction_on with | _ ω =>
  induction z using Submodule.Quotient.induction_on with | _ z =>
  rfl

theorem cohomologyMap_range_iff (P : ScopedGeometricRewritePresentation S) (c : H1 P) :
    c ∈ LinearMap.range (cohomologyMap P) ↔
      ∀ z, homologyMap P z = 0 → pairing P c z = 0 := by
  constructor
  · rintro ⟨d,rfl⟩ z hz
    rw [pairing_compatibility,hz,map_zero]
  · induction c using Submodule.Quotient.induction_on with | _ ω =>
    intro h
    have hg : (ω : Cochain E) ∈ Closed (geometricPresentation S) := by
      apply (geometric_closed_iff_null_periods _).mpr
      intro l
      have hz := h (loopClass P l.val.1 (Quotient.mk _ l.val.2)) (homologyMap_nullLoop P l)
      change inner ℝ (ω : Cochain E) (wordChain l.val.2) = 0 at hz
      rwa [real_inner_comm,wordChain_period] at hz
    exact ⟨(Boundaries (geometricPresentation S)).mkQ ⟨ω,hg⟩,rfl⟩

theorem harmonic_descent_iff (P : ScopedGeometricRewritePresentation S) (h : Harmonic P) :
    (h : Cochain E) ∈ Harmonic (geometricPresentation S) ↔
      ∀ l : NullLoop S, period l.val.2 h = 0 := by
  constructor
  · intro hg
    exact (geometric_closed_iff_null_periods _).mp hg.1
  · intro hn
    exact ⟨(geometric_closed_iff_null_periods _).mpr hn,h.property.2⟩

end ComputationalHodge.GeometricDescent
