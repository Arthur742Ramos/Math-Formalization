module
public import Poisson
@[expose] public section
namespace ComputationalHodge.GreenOperator
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson
open MeasureTheory Set
theorem weightedMean_smul (ρ : RegularDensity) (c : ℝ) (f : Coefficient) :
    weightedMean ρ (c•f)=c*weightedMean ρ f := by
  have h : ρ.val.val*(c•f)=c•(ρ.val.val*f) := by ext q;change _*(c*_) = c*(_*_);ring
  rw [weightedMean,h,mean_smul]
  rfl
/-- Ordinary weighted integral pairing; no Hilbert completion or self-adjoint realization. -/
noncomputable def pairing (ρ : RegularDensity) (f g : Coefficient) : ℝ := mean (ρ.val.val*f*g)
end ComputationalHodge.GreenOperator
