module
public import Harmonic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
@[expose] public section

namespace ComputationalHodge.LoopCharacters
open ComputationalPaths.Path.GeometricTopology
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E}

/-- The ambient fundamental-groupoid class of an actual realized computational trace. -/
noncomputable def traceClass {x y : A} (p : GeometricTrace S.toGeometricStepSystem x y) :
    _root_.Path.Homotopic.Quotient x y :=
  _root_.Path.Homotopic.Quotient.mk (GeometricTrace.realize p)

theorem traceClass_refl (x : A) : traceClass (S := S) (.refl x) =
    _root_.Path.Homotopic.Quotient.refl x := rfl

theorem traceClass_trans {x y z : A} (p : GeometricTrace S.toGeometricStepSystem x y)
    (q : GeometricTrace S.toGeometricStepSystem y z) :
    traceClass (.trans p q) = (traceClass p).trans (traceClass q) :=
  _root_.Path.Homotopic.Quotient.mk_trans _ _

theorem traceClass_symm {x y : A} (p : GeometricTrace S.toGeometricStepSystem x y) :
    traceClass (.symm p) = (traceClass p).symm :=
  _root_.Path.Homotopic.Quotient.mk_symm _

/-- Actual image subgroup in the ambient fundamental group, not a newly stipulated quotient. -/
noncomputable def representedGroup (S : ContinuousGeometricStepSystem A E) (a : A) :
    Subgroup (FundamentalGroup A a) where
  carrier g := ∃ p : GeometricTrace S.toGeometricStepSystem a a, traceClass p = g
  one_mem' := ⟨.refl a,rfl⟩
  mul_mem' := by
    rintro _ _ ⟨p,rfl⟩ ⟨q,rfl⟩
    exact ⟨.trans q p,traceClass_trans q p⟩
  inv_mem' := by
    rintro _ ⟨p,rfl⟩
    exact ⟨.symm p,traceClass_symm p⟩

noncomputable def representedLoop {a : A} (p : GeometricTrace S.toGeometricStepSystem a a) :
    representedGroup S a := ⟨traceClass p,p,rfl⟩

theorem representedLoop_refl (a : A) : representedLoop (S := S) (.refl a) = 1 := rfl

theorem representedLoop_trans {a : A} (p q : GeometricTrace S.toGeometricStepSystem a a) :
    representedLoop (.trans p q) = representedLoop q * representedLoop p :=
  Subtype.ext (traceClass_trans p q)

theorem representedLoop_symm {a : A} (p : GeometricTrace S.toGeometricStepSystem a a) :
    representedLoop (.symm p) = (representedLoop p)⁻¹ := Subtype.ext (traceClass_symm p)

/-- Only computational endpoints, plus the root, need be connected by traces. -/
def Active (S : ContinuousGeometricStepSystem A E) (a x : A) : Prop :=
  x = a ∨ ∃ e : E, S.src e = x ∨ S.tgt e = x

structure Rooting (S : ContinuousGeometricStepSystem A E) (a : A) where
  trace : (x : A) → Active S a x → GeometricTrace S.toGeometricStepSystem a x
  at_root : trace a (Or.inl rfl) = .refl a

theorem active_endpoints {a x y : A} (p : GeometricTrace S.toGeometricStepSystem x y) :
    Active S a x ↔ Active S a y := by
  induction p with
  | refl => rfl
  | single e => exact iff_of_true (Or.inr ⟨e,Or.inl rfl⟩) (Or.inr ⟨e,Or.inr rfl⟩)
  | trans p q hp hq => exact hp.trans hq
  | symm p hp => exact hp.symm

variable [Fintype E]

theorem inactive_period_zero {a x y : A} (p : GeometricTrace S.toGeometricStepSystem x y)
    (hx : ¬ Active S a x) (ω : Cochain E) : period p ω = 0 := by
  induction p with
  | refl => rfl
  | single e => exact (hx (Or.inr ⟨e,Or.inl rfl⟩)).elim
  | trans p q hp hq =>
    change period p ω + period q ω = 0
    rw [hp hx,hq (fun hy => hx ((active_endpoints p).mpr hy)),add_zero]
  | symm p hp =>
    change -period p ω = 0
    rw [hp (fun hy => hx ((active_endpoints p).mp hy)),neg_zero]

/-- Complete geometric relations are actual endpoint-fixed path homotopies. -/
noncomputable def geometricPresentation (S : ContinuousGeometricStepSystem A E) :
    ScopedGeometricRewritePresentation S where
  rule p q := _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q)
  sound_rule h := h

theorem closed_period_homotopic (ω : Closed (geometricPresentation S)) {x y : A}
    (p q : GeometricTrace S.toGeometricStepSystem x y)
    (h : traceClass p = traceClass q) : period p ω = period q ω :=
  closed_rule (geometricPresentation S) ω (_root_.Path.Homotopic.Quotient.eq.mp h)

end ComputationalHodge.LoopCharacters
