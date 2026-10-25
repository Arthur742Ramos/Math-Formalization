module
public import Chains
@[expose] public section
namespace ComputationalHodge.PresentationHomology
open ComputationalPaths.Path.GeometricTopology
open scoped InnerProductSpace
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [Fintype E] [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E}

noncomputable def ChainBoundaries (P : ScopedGeometricRewritePresentation S) :
    Submodule ℝ (Cycles S.toGeometricStepSystem) :=
  (Relations P).comap (Cycles S.toGeometricStepSystem).subtype
abbrev ChainH1 (P : ScopedGeometricRewritePresentation S) :=
  Cycles S.toGeometricStepSystem ⧸ ChainBoundaries P

theorem rewrite_chain_difference (P : ScopedGeometricRewritePresentation S)
    {a b : A} {p q : GeometricTrace S.toGeometricStepSystem a b} (h : ScopedRwEq P p q) :
    wordChain p - wordChain q ∈ Relations P := by
  rw [← Submodule.orthogonal_orthogonal (K := Relations P)]
  intro ω hω
  have hc : ω ∈ Closed P := by rw [closed_eq_relations_orthogonal]; exact hω
  rw [real_inner_comm, inner_sub_left, wordChain_period, wordChain_period,
    period_rewrite P ⟨ω,hc⟩ h, sub_self]

noncomputable def loopCycle {S : GeometricStepSystem A E} {a : A}
    (p : GeometricTrace S a a) : Cycles S :=
  ⟨wordChain p, by change boundary₁ S (wordChain p) = 0; simp [boundary_word]⟩

noncomputable def loopClass (P : ScopedGeometricRewritePresentation S) (a : A) :
    PathClass P a a → ChainH1 P :=
  Quotient.lift (fun p => (ChainBoundaries P).mkQ (loopCycle p))
    (by
      intro p q hpq
      apply (Submodule.Quotient.eq (ChainBoundaries P)).mpr
      exact rewrite_chain_difference P hpq)

end ComputationalHodge.PresentationHomology
