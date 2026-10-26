module
public import Resonance
@[expose] public section
namespace ComputationalHodge.FullCircleRange
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson ComputationalHodge.GreenOperator ComputationalHodge.CompactGreen ComputationalHodge.CircleFredholm ComputationalHodge.ResonanceObstruction ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals MeasureTheory Set
open scoped Topology NNReal unitInterval ContDiff

/-- Actual geometer-sign operator on all C2 coefficients, without normalization. -/
noncomputable def fullShifted (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) : Coefficient :=
  laplacian ρ u-μ•u.val
theorem fullShifted_sub (ρ : RegularDensity) (μ : ℝ) (u v : C2Coefficient) :
    fullShifted ρ μ (u-v)=fullShifted ρ μ u-fullShifted ρ μ v := (congrArg₂ (·-·) (laplacian_sub ρ u v) (smul_sub μ u.val v.val)).trans
    (sub_sub_sub_comm _ _ _ _)
theorem fullShifted_constant (ρ : RegularDensity) (μ c : ℝ) :
    fullShifted ρ μ (constantC2 c)=constant (-μ*c) := by
  rw [fullShifted,laplacian_of_constant ρ (constantC2 c) c rfl]
  ext q
  change (0 : ℝ)-μ*c=(-μ)*c
  ring
theorem weightedMean_fullShifted (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) :
    weightedMean ρ (fullShifted ρ μ u)= -μ*weightedMean ρ u.val := by
  rw [fullShifted,weightedMean_sub,weightedMean_laplacian,weightedMean_smul]
  ring
theorem nonzero_homogeneous_normalized (ρ : RegularDensity) (μ : ℝ) (hμ : μ≠0)
    (v : C2Coefficient) (hv : fullShifted ρ μ v=0) : weightedMean ρ v.val=0 := by
  exact (mul_eq_zero.mp ((weightedMean_fullShifted ρ μ v).symm.trans
    ((congrArg (meanFunctional ρ) hv).trans (map_zero _)))).resolve_left (neg_ne_zero.mpr hμ)
theorem pairing_constant_left (ρ : RegularDensity) (a : ℝ) (v : Coefficient) :
    pairing ρ (constant a) v=a*weightedMean ρ v := by
  have h : ρ.val.val*constant a*v=a•(ρ.val.val*v) := by ext q;change _*a*_ = a*(_*_);ring
  change mean (ρ.val.val*constant a*v)=a*mean (ρ.val.val*v)
  rw [h,mean_smul]
theorem pairing_one_right (ρ : RegularDensity) (f : Coefficient) :
    pairing ρ f (constant 1)=weightedMean ρ f := by
  rw [pairing_comm,pairing_constant_left,one_mul]
theorem zero_solvable_iff_raw (ρ : RegularDensity) (f : Coefficient) :
    (∃ u : C2Coefficient,fullShifted ρ 0 u=f) ↔
      ∀ p : Trace 0 0,lineIntegral (ρ.val.val*f) (fromTrace p)=0 := ⟨fun ⟨u,hu⟩ => (compatible_iff_raw ρ f).mp
    (by change weightedMean ρ f=0;rw [← hu,weightedMean_fullShifted,neg_zero,zero_mul]),
   fun hp => let g : Compatible ρ := ⟨f,(compatible_iff_raw ρ f).mpr hp⟩
     ⟨solution ρ g,by simpa only [fullShifted,zero_smul,sub_zero] using solution_solves ρ g⟩⟩
end ComputationalHodge.FullCircleRange
