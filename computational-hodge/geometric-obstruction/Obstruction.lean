module
public import Descent
public import Mathlib.Analysis.InnerProductSpace.ProdL2
@[expose] public section
namespace ComputationalHodge.GeometricObstruction
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.PresentationHomology ComputationalHodge.GeometricDescent
open scoped InnerProductSpace
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [Fintype E] [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E}

/-- The geometric relations not already removed by the old presentation. -/
noncomputable def Obstruction (P : ScopedGeometricRewritePresentation S) :
    Submodule ℝ (Cochain E) := NullSpan S ⊓ (Relations P)ᗮ

theorem nullSpan_le_cycles : NullSpan S ≤ Cycles S.toGeometricStepSystem := by
  rw [← geometric_relations_eq_nullSpan]
  exact relations_le_cycles _

theorem geometric_harmonic_orthogonal (g : Harmonic (geometricPresentation S)) :
    (g : Cochain E) ∈ (NullSpan S)ᗮ := by
  rw [← geometric_relations_eq_nullSpan,← closed_eq_relations_orthogonal]
  exact g.property.1

theorem correction_mem (P : ScopedGeometricRewritePresentation S) (h : Harmonic P) :
    (h : Cochain E) - (NullSpan S).starProjection h ∈ Harmonic (geometricPresentation S) := by
  constructor
  · rw [closed_eq_relations_orthogonal,geometric_relations_eq_nullSpan]
    exact (NullSpan S).sub_starProjection_mem_orthogonal _
  · have hb := nullSpan_le_cycles ((NullSpan S).starProjection_apply_mem (h : Cochain E))
    rw [cycles_eq_exact_orthogonal] at hb
    exact (Exact S)ᗮ.sub_mem h.property.2 hb

/-- Canonical geometric correction, using the actual nullhomotopic trace span. -/
noncomputable def geometricCorrection (P : ScopedGeometricRewritePresentation S) :
    Harmonic P →ₗ[ℝ] Harmonic (geometricPresentation S) where
  toFun h := ⟨(h : Cochain E) - (NullSpan S).starProjection h,correction_mem P h⟩
  map_add' h k := by
    apply Subtype.ext
    change ((h : Cochain E) + k) - (NullSpan S).starProjection (h + k) = _
    rw [map_add]
    change _ = ((h : Cochain E) - (NullSpan S).starProjection h) +
      ((k : Cochain E) - (NullSpan S).starProjection k)
    abel
  map_smul' r h := by
    apply Subtype.ext
    change r • (h : Cochain E) - (NullSpan S).starProjection (r • (h : Cochain E)) = _
    rw [map_smul]
    exact (smul_sub r (h : Cochain E) ((NullSpan S).starProjection h)).symm

theorem obstruction_mem (P : ScopedGeometricRewritePresentation S) (h : Harmonic P) :
    (NullSpan S).starProjection (h : Cochain E) ∈ Obstruction P := by
  refine ⟨(NullSpan S).starProjection_apply_mem _,?_⟩
  rw [← closed_eq_relations_orthogonal]
  have hg := geometric_closed_le P (geometricCorrection P h).property.1
  have hd := (Closed P).sub_mem h.property.1 hg
  change (NullSpan S).starProjection (h : Cochain E) ∈ Closed P
  change (h : Cochain E) - ((h : Cochain E) - (NullSpan S).starProjection h) ∈ Closed P at hd
  rw [sub_sub_cancel] at hd
  exact hd

noncomputable def obstructionProjection (P : ScopedGeometricRewritePresentation S) :
    Harmonic P →ₗ[ℝ] Obstruction P where
  toFun h := ⟨(NullSpan S).starProjection h,obstruction_mem P h⟩
  map_add' h k := Subtype.ext (map_add (NullSpan S).starProjection (h : Cochain E) (k : Cochain E))
  map_smul' r h := Subtype.ext (map_smul (NullSpan S).starProjection r (h : Cochain E))

theorem harmonic_decomposition (P : ScopedGeometricRewritePresentation S) (h : Harmonic P) :
    (h : Cochain E) = (geometricCorrection P h : Cochain E) + obstructionProjection P h :=
  (sub_add_cancel (h : Cochain E) ((NullSpan S).starProjection h)).symm

theorem geometric_obstruction_orthogonal (P : ScopedGeometricRewritePresentation S)
    (g : Harmonic (geometricPresentation S)) (b : Obstruction P) :
    inner ℝ (g : Cochain E) (b : Cochain E) = 0 :=
  (real_inner_comm _ _).trans (geometric_harmonic_orthogonal g b b.property.1)

theorem geometricCorrection_invariant (P : ScopedGeometricRewritePresentation S) (h : Harmonic P) :
    GeometricInvariant (S := S) (geometricCorrection P h : Cochain E) :=
  (period_descent_iff _).mpr ((geometric_closed_iff_null_periods _).mp
    (geometricCorrection P h).property.1)

theorem obstruction_zero_iff_descent (P : ScopedGeometricRewritePresentation S) (h : Harmonic P) :
    obstructionProjection P h = 0 ↔ GeometricInvariant (S := S) (h : Cochain E) := by
  rw [period_descent_iff,← harmonic_descent_iff P h]
  constructor
  · intro hb
    have he := harmonic_decomposition P h
    rw [hb,ZeroMemClass.coe_zero,add_zero] at he
    exact he ▸ (geometricCorrection P h).property
  · intro hg
    apply Subtype.ext
    change (NullSpan S).starProjection (h : Cochain E) = 0
    have ho : (h : Cochain E) ∈ (NullSpan S)ᗮ := by
      rw [← geometric_relations_eq_nullSpan,← closed_eq_relations_orthogonal]
      exact hg.1
    exact congrArg Subtype.val (Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr ho)

theorem decomposition_unique (P : ScopedGeometricRewritePresentation S) (h : Harmonic P)
    (g : Harmonic (geometricPresentation S)) (b : Obstruction P)
    (he : (h : Cochain E) = (g : Cochain E) + b) :
    g = geometricCorrection P h ∧ b = obstructionProjection P h := by
  have hp : (NullSpan S).starProjection (h : Cochain E) = (b : Cochain E) :=
    Submodule.eq_starProjection_of_mem_orthogonal' b.property.1
      (geometric_harmonic_orthogonal g) (he.trans (add_comm _ _))
  constructor
  · apply Subtype.ext
    change (g : Cochain E) = (h : Cochain E) - (NullSpan S).starProjection h
    rw [hp,he,add_sub_cancel_right]
  · exact Subtype.ext hp.symm

theorem approximation_pythagoras (P : ScopedGeometricRewritePresentation S) (h : Harmonic P)
    (k : Harmonic (geometricPresentation S)) :
    ‖(h : Cochain E) - k‖ ^ 2 = ‖(obstructionProjection P h : Cochain E)‖ ^ 2 +
      ‖(geometricCorrection P h : Cochain E) - k‖ ^ 2 := by
  have he : (h : Cochain E) - k = (obstructionProjection P h : Cochain E) +
      ((geometricCorrection P h : Cochain E) - k) := by
    rw [harmonic_decomposition P h]; abel
  have ho : inner ℝ (obstructionProjection P h : Cochain E)
      ((geometricCorrection P h : Cochain E) - k) = 0 :=
    (real_inner_comm _ _).trans
      (geometric_obstruction_orthogonal P (geometricCorrection P h - k) (obstructionProjection P h))
  rw [he,norm_add_sq_real,ho,mul_zero,add_zero]

theorem correction_error (P : ScopedGeometricRewritePresentation S) (h : Harmonic P) :
    ‖(h : Cochain E) - geometricCorrection P h‖ = ‖(obstructionProjection P h : Cochain E)‖ := by
  rw [harmonic_decomposition P h,add_sub_cancel_left]

theorem correction_closest (P : ScopedGeometricRewritePresentation S) (h : Harmonic P)
    (k : Harmonic (geometricPresentation S)) :
    ‖(h : Cochain E) - geometricCorrection P h‖ ≤ ‖(h : Cochain E) - k‖ := by
  rw [correction_error]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [approximation_pythagoras]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem correction_unique_closest (P : ScopedGeometricRewritePresentation S) (h : Harmonic P)
    (k : Harmonic (geometricPresentation S)) :
    ‖(h : Cochain E) - k‖ = ‖(h : Cochain E) - geometricCorrection P h‖ ↔
      k = geometricCorrection P h := by
  constructor
  · intro he
    rw [correction_error] at he
    have hs := approximation_pythagoras P h k
    rw [he] at hs
    have hz : ‖(geometricCorrection P h : Cochain E) - k‖ ^ 2 = 0 :=
      (add_eq_left.mp hs.symm)
    have hv := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
    exact (Subtype.ext (sub_eq_zero.mp hv)).symm
  · rintro rfl; rfl

end ComputationalHodge.GeometricObstruction
