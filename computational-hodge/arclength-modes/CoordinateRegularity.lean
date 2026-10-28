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


end ComputationalHodge.ArclengthSpectrum
