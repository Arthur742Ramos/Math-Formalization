module
public import Green
@[expose] public section
namespace ComputationalHodge.CircleFredholm
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson
open ComputationalHodge.GreenOperator
/-- Actual normalized twice continuously differentiable circle functions; no Banach claim. -/
abbrev Domain (ρ : RegularDensity) := {u : C2Coefficient // weightedMean ρ u.val=0}
noncomputable def shifted (ρ : RegularDensity) (μ : ℝ) (u : Domain ρ) : Coefficient :=
  laplacian ρ u.val-μ•u.val.val
/-- Resonance is an actual nonzero normalized C2 solution, not an abstract assumption. -/
def Resonant (ρ : RegularDensity) (μ : ℝ) : Prop :=
  ∃ u : Domain ρ,u.val.val≠0 ∧ shifted ρ μ u=0
end ComputationalHodge.CircleFredholm
