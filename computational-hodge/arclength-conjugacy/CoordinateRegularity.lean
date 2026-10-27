module
public import ArclengthCoordinate
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
@[expose] public section

namespace ComputationalHodge.ArclengthSpectrum
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge
open ComputationalHodge.Poisson ComputationalHodge.Arclength
open scoped ContDiff

/-- The existing arclength coordinate has the regularity required for C² pullback. -/
theorem coordinate_contDiff_two (ρ : RegularDensity) :
    ContDiff ℝ 2 (coordinate ρ.val) := by
  have hd : deriv (coordinate ρ.val) =
      fun x => cover ρ.val.val x / mean ρ.val.val :=
    funext fun x => (coordinate_hasDerivAt ρ.val x).deriv
  change ContDiff ℝ ((1 : ℕ∞ω) + 1) (coordinate ρ.val)
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun x => (coordinate_hasDerivAt ρ.val x).differentiableAt, ?_, ?_⟩
  · intro h
    norm_num at h
  · rw [hd]
    exact ρ.property.div_const _

/-- The inverse coordinate is C², using positivity of the actual density. -/
theorem inverse_contDiff_two (ρ : RegularDensity) : ContDiff ℝ 2 (inverse ρ.val) := by
  change ContDiff ℝ 2 ((coordinateHomeomorph ρ.val).symm : ℝ → ℝ)
  exact (coordinateHomeomorph ρ.val).contDiff_symm_deriv
    (fun x => ne_of_gt (div_pos (ρ.val.property _) (mean_pos ρ.val)))
    (coordinate_hasDerivAt ρ.val) (coordinate_contDiff_two ρ)
end ComputationalHodge.ArclengthSpectrum
