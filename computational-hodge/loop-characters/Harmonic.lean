module

public import Periods
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section
namespace ComputationalHodge
open ComputationalPaths.Path.GeometricTopology
open scoped InnerProductSpace
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [Fintype E] [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E}

noncomputable def Harmonic (P : ScopedGeometricRewritePresentation S) : Submodule ℝ (Cochain E) :=
  Closed P ⊓ (Exact S)ᗮ

/-- Boundaries as a subspace of cycles, rather than an ill-typed ambient quotient. -/
def Boundaries (P : ScopedGeometricRewritePresentation S) : Submodule ℝ (Closed P) :=
  (Exact S).comap (Closed P).subtype

abbrev H1 (P : ScopedGeometricRewritePresentation S) := Closed P ⧸ Boundaries P

/-- Constructed by actual finite-dimensional orthogonal projection, with no
Hodge decomposition or representative existence supplied as a hypothesis. -/
noncomputable def harmonicProjection (P : ScopedGeometricRewritePresentation S) :
    Closed P →ₗ[ℝ] Harmonic P where
  toFun ω := ⟨(ω : Cochain E) - (Exact S).starProjection ω,
    (Closed P).sub_mem ω.property (exact_le_closed P <| (Exact S).starProjection_apply_mem _),
    (Exact S).sub_starProjection_mem_orthogonal _⟩
  map_add' ω η := Subtype.ext <|
    (congrArg (fun z : Cochain E => ((ω : Cochain E) + η) - z)
      ((Exact S).starProjection.map_add (ω : Cochain E) (η : Cochain E))).trans
      (add_sub_add_comm (ω : Cochain E) (η : Cochain E)
        ((Exact S).starProjection ω) ((Exact S).starProjection η))
  map_smul' r ω := Subtype.ext <|
    (congrArg (fun z : Cochain E => r • (ω : Cochain E) - z)
      ((Exact S).starProjection.map_smul r (ω : Cochain E))).trans
      (smul_sub r (ω : Cochain E) ((Exact S).starProjection ω)).symm

theorem harmonicProjection_difference (P : ScopedGeometricRewritePresentation S) (ω : Closed P) :
    (ω : Cochain E) - (harmonicProjection P ω : Cochain E) ∈ Exact S := by
  change (ω : Cochain E) - ((ω : Cochain E) - (Exact S).starProjection ω) ∈ Exact S
  simpa only [sub_sub_cancel] using (Exact S).starProjection_apply_mem (ω : Cochain E)

theorem harmonic_exact_zero (P : ScopedGeometricRewritePresentation S) {ω : Cochain E}
    (hω : ω ∈ Harmonic P) (he : ω ∈ Exact S) : ω = 0 := by
  have h : ω ∈ Exact S ⊓ (Exact S)ᗮ := ⟨he, hω.2⟩
  simpa only [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] using h

theorem unique_harmonic_representative (P : ScopedGeometricRewritePresentation S) (ω : Closed P) :
    ∃! h : Harmonic P, (ω : Cochain E) - (h : Cochain E) ∈ Exact S := by
  refine ⟨harmonicProjection P ω, harmonicProjection_difference P ω, ?_⟩
  intro h hh
  have he : (h : Cochain E) - (harmonicProjection P ω : Cochain E) ∈ Exact S := by
    have := (Exact S).sub_mem (harmonicProjection_difference P ω) hh
    convert this using 1
    abel
  have hz := harmonic_exact_zero P
    ((Harmonic P).sub_mem h.property (harmonicProjection P ω).property) he
  exact Subtype.ext (sub_eq_zero.mp hz)

theorem harmonicProjection_eq_zero_iff (P : ScopedGeometricRewritePresentation S) (ω : Closed P) :
    harmonicProjection P ω = 0 ↔ (ω : Cochain E) ∈ Exact S := by
  constructor
  · intro h
    have := harmonicProjection_difference P ω
    simpa only [h, ZeroMemClass.coe_zero, sub_zero] using this
  · intro h
    apply Subtype.ext
    change (ω : Cochain E) - (Exact S).starProjection ω = 0
    rw [Submodule.starProjection_eq_self_iff.mpr h, sub_self]

theorem harmonicProjection_self (P : ScopedGeometricRewritePresentation S) (h : Harmonic P) :
    harmonicProjection P ⟨h, h.property.1⟩ = h := by
  apply Subtype.ext
  change (h : Cochain E) - (Exact S).starProjection h = h
  rw [Submodule.starProjection_apply,
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr h.property.2]
  simp

theorem harmonicProjection_surjective (P : ScopedGeometricRewritePresentation S) :
    Function.Surjective (harmonicProjection P) :=
  fun h => ⟨⟨h, h.property.1⟩, harmonicProjection_self P h⟩

theorem harmonicProjection_kernel (P : ScopedGeometricRewritePresentation S) :
    LinearMap.ker (harmonicProjection P) = Boundaries P := by
  ext ω
  exact harmonicProjection_eq_zero_iff P ω

/-- The actual first presentation cohomology is linearly equivalent to harmonic cochains. -/
noncomputable def hodgeEquiv (P : ScopedGeometricRewritePresentation S) : H1 P ≃ₗ[ℝ] Harmonic P :=
  (Submodule.quotEquivOfEq (Boundaries P) (LinearMap.ker (harmonicProjection P))
    (harmonicProjection_kernel P).symm).trans
    ((harmonicProjection P).quotKerEquivOfSurjective (harmonicProjection_surjective P))

theorem hodgeEquiv_mk (P : ScopedGeometricRewritePresentation S) (ω : Closed P) :
    hodgeEquiv P ((Boundaries P).mkQ ω) = harmonicProjection P ω := rfl

theorem harmonicProjection_preserves_loop_period (P : ScopedGeometricRewritePresentation S)
    (ω : Closed P) {a : A} (p : GeometricTrace S.toGeometricStepSystem a a) :
    period p (harmonicProjection P ω : Cochain E) = period p ω := by
  rcases harmonicProjection_difference P ω with ⟨f, hf⟩
  have h := period_d0 f p
  rw [hf, map_sub, sub_self] at h
  exact (sub_eq_zero.mp h).symm

end ComputationalHodge
