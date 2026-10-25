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

noncomputable def chainHarmonicProjection (P : ScopedGeometricRewritePresentation S) :
    Cycles S.toGeometricStepSystem →ₗ[ℝ] Harmonic P where
  toFun z := ⟨(z : Cochain E) - (Relations P).starProjection z, by
    rw [closed_eq_relations_orthogonal]
    exact (Relations P).sub_starProjection_mem_orthogonal _, by
    rw [← cycles_eq_exact_orthogonal]
    exact (Cycles S.toGeometricStepSystem).sub_mem z.property
      (relations_le_cycles P ((Relations P).starProjection_apply_mem _))⟩
  map_add' z w := by
    apply Subtype.ext
    change (z.val + w.val) - (Relations P).starProjection (z.val + w.val) =
      (z.val - (Relations P).starProjection z.val) + (w.val - (Relations P).starProjection w.val)
    rw [map_add]; abel
  map_smul' r z := by
    apply Subtype.ext
    change r • z.val - (Relations P).starProjection (r • z.val) =
      r • (z.val - (Relations P).starProjection z.val)
    rw [map_smul, smul_sub]

theorem chainProjection_difference (P : ScopedGeometricRewritePresentation S)
    (z : Cycles S.toGeometricStepSystem) :
    (z : Cochain E) - (chainHarmonicProjection P z : Cochain E) ∈ Relations P := by
  change (z : Cochain E) - ((z : Cochain E) - (Relations P).starProjection z) ∈ Relations P
  simpa only [sub_sub_cancel] using (Relations P).starProjection_apply_mem (z : Cochain E)

theorem chainProjection_zero_iff (P : ScopedGeometricRewritePresentation S)
    (z : Cycles S.toGeometricStepSystem) : chainHarmonicProjection P z = 0 ↔
      (z : Cochain E) ∈ Relations P := by
  constructor
  · intro h
    simpa only [h, ZeroMemClass.coe_zero, sub_zero] using chainProjection_difference P z
  · intro h
    apply Subtype.ext
    change (z : Cochain E) - (Relations P).starProjection z = 0
    rw [Submodule.starProjection_eq_self_iff.mpr h, sub_self]

theorem harmonic_mem_cycles (P : ScopedGeometricRewritePresentation S) (h : Harmonic P) :
    (h : Cochain E) ∈ Cycles S.toGeometricStepSystem := by
  rw [cycles_eq_exact_orthogonal]; exact h.property.2

theorem chainProjection_self (P : ScopedGeometricRewritePresentation S) (h : Harmonic P) :
    chainHarmonicProjection P ⟨h, harmonic_mem_cycles P h⟩ = h := by
  apply Subtype.ext
  have hc : (h : Cochain E) ∈ (Relations P)ᗮ := by
    rw [← closed_eq_relations_orthogonal]; exact h.property.1
  change (h : Cochain E) - (Relations P).starProjection h = h
  rw [Submodule.starProjection_apply,
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hc]
  simp

theorem chainProjection_surjective (P : ScopedGeometricRewritePresentation S) :
    Function.Surjective (chainHarmonicProjection P) :=
  fun h => ⟨⟨h, harmonic_mem_cycles P h⟩, chainProjection_self P h⟩

theorem chainProjection_kernel (P : ScopedGeometricRewritePresentation S) :
    LinearMap.ker (chainHarmonicProjection P) = ChainBoundaries P := by
  ext z; exact chainProjection_zero_iff P z

noncomputable def homologyHodgeEquiv (P : ScopedGeometricRewritePresentation S) :
    ChainH1 P ≃ₗ[ℝ] Harmonic P :=
  (Submodule.quotEquivOfEq (ChainBoundaries P) (LinearMap.ker (chainHarmonicProjection P))
    (chainProjection_kernel P).symm).trans
    ((chainHarmonicProjection P).quotKerEquivOfSurjective (chainProjection_surjective P))

theorem homologyHodge_mk (P : ScopedGeometricRewritePresentation S)
    (z : Cycles S.toGeometricStepSystem) :
    homologyHodgeEquiv P ((ChainBoundaries P).mkQ z) = chainHarmonicProjection P z := rfl

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

theorem loopClass_compose (P : ScopedGeometricRewritePresentation S) {a : A}
    (p q : PathClass P a a) : loopClass P a (compose P p q) = loopClass P a p + loopClass P a q := by
  induction p using Quotient.inductionOn with | _ p =>
  induction q using Quotient.inductionOn with | _ q =>
  change (ChainBoundaries P).mkQ (loopCycle (.trans p q)) =
    (ChainBoundaries P).mkQ (loopCycle p) + (ChainBoundaries P).mkQ (loopCycle q)
  rw [show loopCycle (.trans p q) = loopCycle p + loopCycle q from Subtype.ext rfl, map_add]

theorem loopClass_refl (P : ScopedGeometricRewritePresentation S) (a : A) :
    loopClass P a (Quotient.mk _ (.refl a)) = 0 := by
  change (ChainBoundaries P).mkQ (loopCycle (.refl a)) = 0
  rw [show loopCycle (.refl a) = 0 from Subtype.ext rfl, map_zero]

theorem loopClass_symm (P : ScopedGeometricRewritePresentation S) {a : A}
    (p : GeometricTrace S.toGeometricStepSystem a a) :
    loopClass P a (Quotient.mk _ (.symm p)) = -loopClass P a (Quotient.mk _ p) := by
  change (ChainBoundaries P).mkQ (loopCycle (.symm p)) = -(ChainBoundaries P).mkQ (loopCycle p)
  rw [show loopCycle (.symm p) = -loopCycle p from Subtype.ext rfl, map_neg]

def reverse (P : ScopedGeometricRewritePresentation S) {a b : A} : PathClass P a b → PathClass P b a :=
  Quotient.lift (fun p => Quotient.mk _ (.symm p)) (fun _ _ h => Quotient.sound (.symm_congr h))

theorem loopClass_reverse (P : ScopedGeometricRewritePresentation S) {a : A}
    (p : PathClass P a a) : loopClass P a (reverse P p) = -loopClass P a p := by
  induction p using Quotient.inductionOn with | _ p => exact loopClass_symm P p

theorem loopClasses_span (P : ScopedGeometricRewritePresentation S) :
    Submodule.span ℝ (Set.range fun l : Σ a, PathClass P a a => loopClass P l.1 l.2) = ⊤ := by
  let L := Submodule.span ℝ (Set.range fun l : Σ a, PathClass P a a => loopClass P l.1 l.2)
  have hs : LoopSpan S.toGeometricStepSystem ≤
      (L.comap (ChainBoundaries P).mkQ).map (Cycles S.toGeometricStepSystem).subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,p⟩,rfl⟩
    exact ⟨loopCycle p, Submodule.subset_span ⟨⟨a,Quotient.mk _ p⟩,rfl⟩,rfl⟩
  apply top_unique
  intro c _
  induction c using Submodule.Quotient.induction_on with | _ z =>
  have hz : (z : Cochain E) ∈ LoopSpan S.toGeometricStepSystem := by
    rw [loopSpan_eq_cycles]; exact z.property
  obtain ⟨w,hw,heq⟩ := hs hz
  have hwz : w = z := Subtype.ext heq
  change (ChainBoundaries P).mkQ w ∈ L at hw
  change (ChainBoundaries P).mkQ z ∈ L
  simpa only [hwz] using hw

end ComputationalHodge.PresentationHomology
