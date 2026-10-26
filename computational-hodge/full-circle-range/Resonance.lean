module
public import Fredholm
@[expose] public section
namespace ComputationalHodge.ResonanceObstruction
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson ComputationalHodge.GreenOperator ComputationalHodge.CircleFredholm ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals ComputationalHodge.LoopCharacters MeasureTheory Set
open scoped Topology NNReal unitInterval ContDiff

theorem pairing_comm (ρ : RegularDensity) (f g : Coefficient) : pairing ρ f g=pairing ρ g f := congrArg mean (mul_right_comm ρ.val.val f g)

theorem pairing_sub_left (ρ : RegularDensity) (f g h : Coefficient) :
    pairing ρ (f-g) h=pairing ρ f h-pairing ρ g h := by
  unfold pairing
  rw [mul_sub,sub_mul,mean_sub]

theorem pairing_smul_left (ρ : RegularDensity) (c : ℝ) (f g : Coefficient) :
    pairing ρ (c•f) g=c*pairing ρ f g := by
  unfold pairing
  rw [mul_smul_comm,smul_mul_assoc,mean_smul]

theorem pairing_smul_right (ρ : RegularDensity) (c : ℝ) (f g : Coefficient) :
    pairing ρ f (c•g)=c*pairing ρ f g := by
  rw [pairing_comm,pairing_smul_left,pairing_comm ρ g f]
theorem pairing_positive (ρ : RegularDensity) (f : Coefficient) (hf : f≠0) : 0<pairing ρ f f := by
  obtain ⟨q,hq⟩ : ∃ q,f q≠0 := by simpa using DFunLike.exists_ne hf
  rw [pairing,mean_circle]
  exact integral_pos_of_integrable_nonneg_nonzero (ρ.val.val*f*f).continuous
    (continuous_integrable (ρ.val.val*f*f).continuous)
    (fun t => by change 0≤ρ.val.val t*f t*f t;simpa only [mul_assoc] using mul_nonneg (ρ.val.property t).le (mul_self_nonneg (f t)))
    (show ρ.val.val q*f q*f q≠0 from mul_ne_zero (mul_ne_zero (density_ne ρ.val q) hq) hq)

theorem laplacian_symmetric (ρ : RegularDensity) (u v : C2Coefficient) :
    pairing ρ (laplacian ρ u) v.val=pairing ρ u.val (laplacian ρ v) :=
  pairing_symmetry ρ u v

theorem forcing_orthogonal (ρ : RegularDensity) (μ : ℝ) (u v : C2Coefficient) (f : Coefficient)
    (hv : laplacian ρ v=μ•v.val) (hu : laplacian ρ u-μ•u.val=f) : pairing ρ f v.val=0 := by
  rw [← hu,pairing_sub_left,laplacian_symmetric,hv,pairing_smul_right,pairing_smul_left,sub_self]
end ComputationalHodge.ResonanceObstruction
