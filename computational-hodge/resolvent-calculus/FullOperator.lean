module
public import Fredholm
@[expose] public section
namespace ComputationalHodge.FullCircleRange
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson ComputationalHodge.GreenOperator ComputationalHodge.CompactGreen ComputationalHodge.CircleFredholm ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals MeasureTheory Set
open scoped Topology NNReal unitInterval ContDiff

/-- Actual geometer-sign operator on all C2 coefficients, without normalization. -/
noncomputable def fullShifted (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) : Coefficient :=
  laplacian ρ u-μ•u.val
theorem fullShifted_sub (ρ : RegularDensity) (μ : ℝ) (u v : C2Coefficient) :
    fullShifted ρ μ (u-v)=fullShifted ρ μ u-fullShifted ρ μ v := (congrArg₂ (·-·) (laplacian_sub ρ u v) (smul_sub μ u.val v.val)).trans
    (sub_sub_sub_comm _ _ _ _)
end ComputationalHodge.FullCircleRange
