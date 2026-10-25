module
public import Homology
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
@[expose] public section

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
