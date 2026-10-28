module
public import Resonance
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.MonotoneContinuity
@[expose] public section
namespace ComputationalHodge.Arclength
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.LoopCharacters
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts
open ComputationalHodge.MetricHodge
open MeasureTheory Set
open scoped Topology NNReal unitInterval

noncomputable def coordinate (ρ : Density) (x : ℝ) : ℝ := primitive ρ.val x/mean ρ.val
theorem coordinate_hasDerivAt (ρ : Density) (x : ℝ) :
    HasDerivAt (coordinate ρ) (cover ρ.val x/mean ρ.val) x :=
  (primitive_hasDerivAt ρ.val x).div_const _
theorem coordinate_zero (ρ : Density) : coordinate ρ 0=0 := by simp [coordinate,primitive]
theorem coordinate_shift (ρ : Density) (x : ℝ) (n : ℤ) :
    coordinate ρ (x+n)=coordinate ρ x+n := by
  have h := (cover_periodic ρ.val).intervalIntegral_add_zsmul_eq n x
    (fun a b => (cover_continuous ρ.val).intervalIntegrable a b)
  rw [(cover_periodic ρ.val).intervalIntegral_add_eq x 0] at h
  simp only [zero_add,zsmul_eq_mul,mul_one] at h
  have ha := intervalIntegral.integral_add_adjacent_intervals
    ((cover_continuous ρ.val).intervalIntegrable (μ:=volume) 0 x)
    ((cover_continuous ρ.val).intervalIntegrable (μ:=volume) x (x+n))
  unfold coordinate primitive
  rw [← ha,h]
  change ((∫ t in (0 : ℝ)..x,cover ρ.val t)+(n : ℝ)*mean ρ.val)/mean ρ.val=_
  field_simp [ne_of_gt (mean_pos ρ)]
theorem coordinate_int (ρ : Density) (n : ℤ) : coordinate ρ (n : ℝ)=n := by
  simpa [coordinate_zero] using coordinate_shift ρ 0 n
theorem coordinate_strictMono (ρ : Density) : StrictMono (coordinate ρ) :=
  strictMono_of_hasDerivAt_pos (coordinate_hasDerivAt ρ)
    (fun _ => div_pos (ρ.property _) (mean_pos ρ))
theorem coordinate_surjective (ρ : Density) : Function.Surjective (coordinate ρ) := by
  intro y
  have hc : Continuous (coordinate ρ) := continuous_iff_continuousAt.mpr (fun x => (coordinate_hasDerivAt ρ x).continuousAt)
  have ha : ((⌊y⌋ : ℤ) : ℝ)≤((⌊y⌋+1 : ℤ) : ℝ) := by norm_num
  have hy : y∈Icc (coordinate ρ (⌊y⌋ : ℤ)) (coordinate ρ ((⌊y⌋+1 : ℤ) : ℝ)) := by
    rw [coordinate_int,coordinate_int]
    exact ⟨Int.floor_le y,by exact_mod_cast (Int.lt_floor_add_one y).le⟩
  obtain ⟨x,_,hx⟩:=intermediate_value_Icc ha hc.continuousOn hy
  exact ⟨x,hx⟩
noncomputable def coordinateHomeomorph (ρ : Density) : ℝ ≃ₜ ℝ :=
  ((coordinate_strictMono ρ).orderIsoOfSurjective (coordinate ρ) (coordinate_surjective ρ)).toHomeomorph
noncomputable def inverse (ρ : Density) : ℝ→ℝ := (coordinateHomeomorph ρ).symm
theorem coordinate_inverse (ρ : Density) (x : ℝ) : coordinate ρ (inverse ρ x)=x :=
  (coordinateHomeomorph ρ).apply_symm_apply x
theorem inverse_coordinate (ρ : Density) (x : ℝ) : inverse ρ (coordinate ρ x)=x :=
  (coordinateHomeomorph ρ).symm_apply_apply x

end ComputationalHodge.Arclength
