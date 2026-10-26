module
public import CompactGreen
@[expose] public section
namespace ComputationalHodge.CircleFredholm
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson ComputationalHodge.GreenOperator ComputationalHodge.CompactGreen ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals MeasureTheory Set Function Topology Module
open scoped Topology NNReal unitInterval ContDiff

noncomputable def reduced (ρ : RegularDensity) (μ : ℝ) : Compatible ρ →L[ℝ] Compatible ρ :=
  1-μ•greenMap ρ
end ComputationalHodge.CircleFredholm
