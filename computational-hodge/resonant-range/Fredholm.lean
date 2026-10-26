module
public import CompactGreen
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
@[expose] public section
namespace ComputationalHodge.CircleFredholm
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson ComputationalHodge.GreenOperator ComputationalHodge.CompactGreen ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals MeasureTheory Set Function Topology Module
open scoped Topology NNReal unitInterval ContDiff

/-- Actual normalized twice continuously differentiable circle functions; no Banach claim. -/
abbrev Domain (ρ : RegularDensity) := {u : C2Coefficient // weightedMean ρ u.val=0}
noncomputable def liftData (ρ : RegularDensity) (f : Compatible ρ) : Domain ρ :=
  ⟨solution ρ f,solution_mean_zero ρ f⟩
noncomputable def reduced (ρ : RegularDensity) (μ : ℝ) : Compatible ρ →L[ℝ] Compatible ρ :=
  1-μ•greenMap ρ
noncomputable def shifted (ρ : RegularDensity) (μ : ℝ) (u : Domain ρ) : Coefficient :=
  laplacian ρ u.val-μ•u.val.val
theorem shifted_lift (ρ : RegularDensity) (μ : ℝ) (f : Compatible ρ) :
    shifted ρ μ (liftData ρ f)=(reduced ρ μ f).val := by
  change laplacian ρ (solution ρ f)-μ•(solution ρ f).val=f.val-μ•(solution ρ f).val
  rw [solution_solves]

theorem shifted_compatible (ρ : RegularDensity) (μ : ℝ) (u : Domain ρ) :
    shifted ρ μ u∈compatibleSpace ρ :=
  (compatibleSpace ρ).sub_mem (weightedMean_laplacian ρ u.val)
    ((compatibleSpace ρ).smul_mem μ u.property)
end ComputationalHodge.CircleFredholm
