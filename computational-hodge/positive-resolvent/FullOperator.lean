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
theorem weightedMean_fullShifted (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) :
    weightedMean ρ (fullShifted ρ μ u)= -μ*weightedMean ρ u.val := by
  rw [fullShifted,weightedMean_sub,weightedMean_laplacian,weightedMean_smul]
  ring
theorem zero_solvable_iff_raw (ρ : RegularDensity) (f : Coefficient) :
    (∃ u : C2Coefficient,fullShifted ρ 0 u=f) ↔
      ∀ p : Trace 0 0,lineIntegral (ρ.val.val*f) (fromTrace p)=0 := ⟨fun ⟨u,hu⟩ => (compatible_iff_raw ρ f).mp
    (by change weightedMean ρ f=0;rw [← hu,weightedMean_fullShifted,neg_zero,zero_mul]),
   fun hp => let g : Compatible ρ := ⟨f,(compatible_iff_raw ρ f).mpr hp⟩
     ⟨solution ρ g,by simpa only [fullShifted,zero_smul,sub_zero] using solution_solves ρ g⟩⟩
end ComputationalHodge.FullCircleRange
