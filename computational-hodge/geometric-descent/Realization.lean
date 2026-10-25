module
public import Duality
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
@[expose] public section
namespace ComputationalPaths.Path.GeometricTopology
namespace ScopedRwEq

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  {S : ContinuousGeometricStepSystem A Step}
  (P : ScopedGeometricRewritePresentation S)

/-- Every scoped rewrite derivation is sound for geometric realization. -/
theorem sound
    {a b : A}
    {p q : GeometricTrace S.toGeometricStepSystem a b}
    (h : ScopedRwEq P p q) :
    _root_.Path.Homotopic
      (GeometricTrace.realize p) (GeometricTrace.realize q) := by
  induction h with
  | refl p => exact ⟨_root_.Path.Homotopy.refl (GeometricTrace.realize p)⟩
  | generator h => exact P.sound_rule h
  | symm h ih =>
      rcases ih with ⟨ih⟩
      exact ⟨ih.symm⟩
  | trans h₁ h₂ ih₁ ih₂ =>
      rcases ih₁ with ⟨ih₁⟩
      rcases ih₂ with ⟨ih₂⟩
      exact ⟨ih₁.trans ih₂⟩
  | trans_congr h₁ h₂ ih₁ ih₂ =>
      rcases ih₁ with ⟨ih₁⟩
      rcases ih₂ with ⟨ih₂⟩
      exact ⟨ih₁.hcomp ih₂⟩
  | symm_congr h ih =>
      rcases ih with ⟨ih⟩
      exact ⟨ih.symm₂⟩
  | refl_trans p =>
      exact ⟨by simpa [GeometricTrace.realize] using
        (_root_.Path.Homotopy.reflTrans (GeometricTrace.realize p))⟩
  | trans_refl p =>
      exact ⟨by simpa [GeometricTrace.realize] using
        (_root_.Path.Homotopy.transRefl (GeometricTrace.realize p))⟩
  | trans_assoc p q r =>
      exact ⟨by simpa [GeometricTrace.realize] using
        (_root_.Path.Homotopy.transAssoc
          (GeometricTrace.realize p) (GeometricTrace.realize q)
          (GeometricTrace.realize r))⟩
  | symm_trans p =>
      exact ⟨by simpa [GeometricTrace.realize] using
        (_root_.Path.Homotopy.reflSymmTrans
          (GeometricTrace.realize p)).symm⟩
  | trans_symm p =>
      exact ⟨by simpa [GeometricTrace.realize] using
        (_root_.Path.Homotopy.reflTransSymm
          (GeometricTrace.realize p)).symm⟩
  | symm_symm p =>
      exact ⟨by simpa [GeometricTrace.realize] using
        (_root_.Path.Homotopy.refl (GeometricTrace.realize p))⟩
  | symm_refl a =>
      exact ⟨by simpa [GeometricTrace.realize] using
        (_root_.Path.Homotopy.refl (_root_.Path.refl a))⟩
  | symm_comp p q =>
      exact ⟨by simpa [GeometricTrace.realize] using
        (_root_.Path.Homotopy.refl
          (_root_.Path.trans (GeometricTrace.realize q).symm
            (GeometricTrace.realize p).symm))⟩

end ScopedRwEq
end ComputationalPaths.Path.GeometricTopology

namespace ComputationalHodge.GeometricDescent
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.PresentationHomology
open scoped InnerProductSpace
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [Fintype E] [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E}

/-- The finite-system analogue of the user's universal geometric presentation. -/
noncomputable def geometricPresentation (S : ContinuousGeometricStepSystem A E) :
    ScopedGeometricRewritePresentation S where
  rule p q := _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q)
  sound_rule h := h

omit [Fintype E] in
theorem geometric_rewrite_iff {a b : A} {p q : GeometricTrace S.toGeometricStepSystem a b} :
    ScopedRwEq (geometricPresentation S) p q ↔
      _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q) :=
  ⟨ScopedRwEq.sound _, fun h => ScopedRwEq.generator (P := geometricPresentation S) h⟩

noncomputable def realization (P : ScopedGeometricRewritePresentation S) {a b : A} :
    PathClass P a b → _root_.Path.Homotopic.Quotient a b :=
  Quotient.lift (fun p => _root_.Path.Homotopic.Quotient.mk (GeometricTrace.realize p))
    (fun _ _ h => Quotient.sound (ScopedRwEq.sound P h))

omit [Fintype E] in
theorem realization_mk (P : ScopedGeometricRewritePresentation S) {a b : A}
    (p : GeometricTrace S.toGeometricStepSystem a b) :
    realization P (Quotient.mk _ p) = _root_.Path.Homotopic.Quotient.mk (GeometricTrace.realize p) := rfl

omit [Fintype E] in
theorem geometric_realization_injective {a b : A} :
    Function.Injective (realization (geometricPresentation S) (a := a) (b := b)) := by
  intro p q h
  induction p using Quotient.inductionOn with | _ p =>
  induction q using Quotient.inductionOn with | _ q =>
  exact Quotient.sound (geometric_rewrite_iff.mpr (_root_.Path.Homotopic.Quotient.exact h))

noncomputable def RealizedArrow (S : ContinuousGeometricStepSystem A E) (a b : A) :=
  Set.range (fun p : GeometricTrace S.toGeometricStepSystem a b =>
    _root_.Path.Homotopic.Quotient.mk (GeometricTrace.realize p))

noncomputable def representedEquiv {a b : A} :
    PathClass (geometricPresentation S) a b ≃ RealizedArrow S a b :=
  Equiv.ofBijective (fun p => ⟨realization (geometricPresentation S) p,by
    induction p using Quotient.inductionOn with | _ p => exact ⟨p,rfl⟩⟩)
    ⟨fun _ _ h => geometric_realization_injective (congrArg Subtype.val h),by
      rintro ⟨x,p,hp⟩
      exact ⟨Quotient.mk _ p,Subtype.ext hp⟩⟩

omit [Fintype E] in
theorem representedEquiv_mk {a b : A} (p : GeometricTrace S.toGeometricStepSystem a b) :
    (representedEquiv (Quotient.mk _ p)).val =
      _root_.Path.Homotopic.Quotient.mk (GeometricTrace.realize p) := rfl

def NullLoop (S : ContinuousGeometricStepSystem A E) :=
  {l : Σ a, GeometricTrace S.toGeometricStepSystem a a //
    _root_.Path.Homotopic (GeometricTrace.realize l.2) (_root_.Path.refl l.1)}

noncomputable def NullSpan (S : ContinuousGeometricStepSystem A E) : Submodule ℝ (Cochain E) :=
  Submodule.span ℝ (Set.range (fun l : NullLoop S => wordChain l.val.2))

omit [Fintype E] in
theorem difference_nullhomotopic {a b : A} {p q : GeometricTrace S.toGeometricStepSystem a b}
    (h : _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q)) :
    _root_.Path.Homotopic (GeometricTrace.realize (.trans p (.symm q))) (_root_.Path.refl a) := by
  exact (h.hcomp (_root_.Path.Homotopic.refl _)).trans
    ⟨(_root_.Path.Homotopy.reflTransSymm (GeometricTrace.realize q)).symm⟩

theorem geometric_relations_eq_nullSpan : Relations (geometricPresentation S) = NullSpan S := by
  rw [relations_eq_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨c,rfl⟩
    have h := Submodule.subset_span (R := ℝ)
      (show wordChain (.trans c.left (.symm c.right)) ∈
        Set.range (fun l : NullLoop S => wordChain l.val.2) from
        ⟨⟨⟨c.src,.trans c.left (.symm c.right)⟩,difference_nullhomotopic c.rule⟩,rfl⟩)
    simpa only [NullSpan,wordChain, sub_eq_add_neg] using h
  · apply Submodule.span_le.mpr
    rintro _ ⟨l,rfl⟩
    have h := Submodule.subset_span (R := ℝ)
      (show wordChain l.val.2 - wordChain (.refl l.val.1) ∈
        Set.range (fun c : Cell (geometricPresentation S) => wordChain c.left - wordChain c.right) from
        ⟨⟨l.val.1,l.val.1,l.val.2,.refl l.val.1,l.property⟩,rfl⟩)
    simpa only [wordChain,sub_zero] using h

theorem presentation_relations_le_nullSpan (P : ScopedGeometricRewritePresentation S) :
    Relations P ≤ NullSpan S := by
  rw [relations_eq_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨c,rfl⟩
  rw [← geometric_relations_eq_nullSpan,relations_eq_span]
  exact Submodule.subset_span ⟨⟨c.src,c.tgt,c.left,c.right,P.sound_rule c.rule⟩,rfl⟩

end ComputationalHodge.GeometricDescent
