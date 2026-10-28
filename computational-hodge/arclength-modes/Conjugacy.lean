module
public import CoordinateRegularity
@[expose] public section

namespace ComputationalHodge.ArclengthSpectrum
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge
open ComputationalHodge.Poisson ComputationalHodge.Arclength
open ComputationalHodge.ResonanceObstruction
open scoped ContDiff

theorem coordinate_cover_periodic (ρ : RegularDensity) (u : Coefficient) :
    Function.Periodic (fun x => cover u (coordinate ρ.val x)) 1 := by
  intro x
  have h : coordinate ρ.val (x + 1) = coordinate ρ.val x + 1 := by
    simpa using coordinate_shift ρ.val x 1
  change cover u (coordinate ρ.val (x + 1)) = cover u (coordinate ρ.val x)
  rw [h]
  exact cover_periodic u _

/-- Pullback along the actual normalized arclength coordinate. -/
noncomputable def pullback (ρ : RegularDensity) (u : Coefficient) : Coefficient where
  toFun := (coordinate_cover_periodic ρ u).lift
  continuous_toFun := ((cover_continuous u).comp (coordinate_contDiff_two ρ).continuous).quotient_liftOn' _

theorem cover_pullback (ρ : RegularDensity) (u : Coefficient) (x : ℝ) :
    cover (pullback ρ u) x = cover u (coordinate ρ.val x) := rfl

noncomputable def pullbackC2 (ρ : RegularDensity) (u : C2Coefficient) : C2Coefficient :=
  ⟨pullback ρ u.val, by
    change ContDiff ℝ 2 (fun x => cover u.val (coordinate ρ.val x))
    exact (show ContDiff ℝ 2 (cover u.val) from u.property).comp (coordinate_contDiff_two ρ)⟩

/-- Conjugacy for the actual positive weighted circle Laplacian on every C² coefficient. -/
theorem laplacian_pullback (ρ : RegularDensity) (u : C2Coefficient) :
    laplacian ρ (pullbackC2 ρ u) =
      (mean ρ.val.val)⁻¹ ^ 2 • pullback ρ (laplacian flatDensity u) := by
  have hm : mean ρ.val.val ≠ 0 := ne_of_gt (mean_pos ρ.val)
  have hp : ∀ x, cover ρ.val.val x ≠ 0 := fun x => density_ne ρ.val (x : CircleHodge.Circle)
  have hd : deriv (cover (pullbackC2 ρ u).val) =
      fun t => deriv (cover u.val) (coordinate ρ.val t) * (cover ρ.val.val t / mean ρ.val.val) := by
    funext t
    exact (((contDiff_one_iff_deriv.mp (c2_c1 u)).1 (coordinate ρ.val t)).hasDerivAt.comp t
      (coordinate_hasDerivAt ρ.val t)).deriv
  have hf : (fun t => deriv (cover (pullbackC2 ρ u).val) t / cover ρ.val.val t) =
      fun t => deriv (cover u.val) (coordinate ρ.val t) / mean ρ.val.val := by
    funext t
    rw [hd]
    field_simp [hm, hp t]
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change cover (laplacian ρ (pullbackC2 ρ u)) x =
    (mean ρ.val.val)⁻¹ ^ 2 * cover (pullback ρ (laplacian flatDensity u)) x
  rw [laplacian_cover, cover_pullback, laplacian_cover, hf]
  change -(deriv (fun t => deriv (cover u.val) (coordinate ρ.val t) / mean ρ.val.val) x) /
      cover ρ.val.val x = (mean ρ.val.val)⁻¹ ^ 2 *
        (-(deriv (fun t => deriv (cover u.val) t / (1 : ℝ)) (coordinate ρ.val x)) / 1)
  simp only [div_one]
  have h := ((((contDiff_one_iff_deriv.mp (c2_deriv_c1 u)).1 (coordinate ρ.val x)).hasDerivAt.comp x
    (coordinate_hasDerivAt ρ.val x)).div_const (mean ρ.val.val)).deriv
  change deriv (fun t => deriv (cover u.val) (coordinate ρ.val t) / mean ρ.val.val) x = _ at h
  rw [h]
  field_simp [hm, hp x]
end ComputationalHodge.ArclengthSpectrum
