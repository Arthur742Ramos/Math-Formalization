module
public import Conjugacy
@[expose] public section
namespace ComputationalHodge.ArclengthSpectrum
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge
open ComputationalHodge.Poisson ComputationalHodge.Arclength

theorem inverse_shift (ρ : RegularDensity) (x : ℝ) (n : ℤ) :
    inverse ρ.val (x + n) = inverse ρ.val x + n := by
  apply (coordinate_strictMono ρ.val).injective
  rw [coordinate_inverse, coordinate_shift, coordinate_inverse]

theorem coordinate_circle_periodic (ρ : RegularDensity) :
    Function.Periodic (fun x : ℝ => (coordinate ρ.val x : CircleHodge.Circle)) 1 := by
  intro x
  change (coordinate ρ.val (x + 1) : CircleHodge.Circle) = (coordinate ρ.val x : CircleHodge.Circle)
  have h : coordinate ρ.val (x + 1) = coordinate ρ.val x + 1 := by
    simpa using coordinate_shift ρ.val x 1
  rw [h]
  exact AddCircle.coe_add_period 1 _

theorem inverse_circle_periodic (ρ : RegularDensity) :
    Function.Periodic (fun x : ℝ => (inverse ρ.val x : CircleHodge.Circle)) 1 := by
  intro x
  change (inverse ρ.val (x + 1) : CircleHodge.Circle) = (inverse ρ.val x : CircleHodge.Circle)
  have h : inverse ρ.val (x + 1) = inverse ρ.val x + 1 := by
    simpa using inverse_shift ρ x 1
  rw [h]
  exact AddCircle.coe_add_period 1 _

/-- The actual based quotient-circle homeomorphism induced by arclength. -/
noncomputable def circleCoordinate (ρ : RegularDensity) : CircleHodge.Circle ≃ₜ CircleHodge.Circle where
  toFun := (coordinate_circle_periodic ρ).lift
  invFun := (inverse_circle_periodic ρ).lift
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with | _ x =>
    change ((inverse ρ.val (coordinate ρ.val x) : ℝ) : CircleHodge.Circle) = (x : CircleHodge.Circle)
    rw [inverse_coordinate]
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with | _ x =>
    change ((coordinate ρ.val (inverse ρ.val x) : ℝ) : CircleHodge.Circle) = (x : CircleHodge.Circle)
    rw [coordinate_inverse]
  continuous_toFun := ((AddCircle.continuous_mk' (1 : ℝ)).comp (coordinate_contDiff_two ρ).continuous).quotient_liftOn' _
  continuous_invFun := ((AddCircle.continuous_mk' (1 : ℝ)).comp (inverse_contDiff_two ρ).continuous).quotient_liftOn' _

theorem circleCoordinate_mk (ρ : RegularDensity) (x : ℝ) :
    circleCoordinate ρ (x : CircleHodge.Circle) = (coordinate ρ.val x : CircleHodge.Circle) := rfl
theorem circleCoordinate_zero (ρ : RegularDensity) : circleCoordinate ρ 0 = 0 := by
  change (coordinate ρ.val 0 : CircleHodge.Circle) = 0
  rw [coordinate_zero]
  rfl

theorem pullback_apply (ρ : RegularDensity) (u : Coefficient) (q : CircleHodge.Circle) :
    pullback ρ u q = u (circleCoordinate ρ q) := by
  induction q using Quotient.inductionOn with | _ x => rfl

/-- Pullback has the inverse induced by the actual inverse coordinate. -/
noncomputable def inversePullback (ρ : RegularDensity) (u : Coefficient) : Coefficient where
  toFun q := u ((circleCoordinate ρ).symm q)
  continuous_toFun := u.continuous.comp (circleCoordinate ρ).symm.continuous

theorem pullback_inversePullback (ρ : RegularDensity) (u : Coefficient) :
    pullback ρ (inversePullback ρ u) = u := by
  ext q
  rw [pullback_apply]
  change u ((circleCoordinate ρ).symm (circleCoordinate ρ q)) = u q
  rw [Homeomorph.symm_apply_apply]

theorem inversePullback_pullback (ρ : RegularDensity) (u : Coefficient) :
    inversePullback ρ (pullback ρ u) = u := by
  ext q
  change pullback ρ u ((circleCoordinate ρ).symm q) = u q
  rw [pullback_apply, Homeomorph.apply_symm_apply]

noncomputable def inversePullbackC2 (ρ : RegularDensity) (u : C2Coefficient) : C2Coefficient :=
  ⟨inversePullback ρ u.val, by
    change ContDiff ℝ 2 (fun x => cover u.val (inverse ρ.val x))
    exact (show ContDiff ℝ 2 (cover u.val) from u.property).comp (inverse_contDiff_two ρ)⟩

/-- The inverse is constructed from the inverse arclength coordinate. -/
noncomputable def pullbackC2Equiv (ρ : RegularDensity) : C2Coefficient ≃ C2Coefficient where
  toFun := pullbackC2 ρ
  invFun := inversePullbackC2 ρ
  left_inv := by
    intro u
    apply Subtype.ext
    exact inversePullback_pullback ρ u.val
  right_inv := by
    intro u
    apply Subtype.ext
    exact pullback_inversePullback ρ u.val
end ComputationalHodge.ArclengthSpectrum
