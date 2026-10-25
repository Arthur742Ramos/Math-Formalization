module
public import ACPeriods
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
@[expose] public section
namespace ComputationalHodge.ACLifts
open ComputationalHodge.CircleHodge
open MeasureTheory Set
open scoped NNReal Topology
/-- An integral primitive, not a Lipschitz assumption at the singular starting point. -/
noncomputable def rootCurve (t : ℝ) : ℝ :=
  (1/2 : ℝ)*(∫ x in (0 : ℝ)..t,x^(-1/2 : ℝ))
theorem rootCurve_ac : AbsolutelyContinuousOnInterval rootCurve 0 1 := by
  exact ((intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
    (r := (-1/2 : ℝ)) (by norm_num)).absolutelyContinuousOnInterval_intervalIntegral
      (by simp)).const_mul (1/2)
theorem rootCurve_eq_sqrt (t : ℝ) : rootCurve t=Real.sqrt t := by
  unfold rootCurve
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1/2))]
  norm_num
  rw [Real.sqrt_eq_rpow]
  ring
noncomputable def rootLift : ACLift :=
  ⟨rootCurve,rootCurve_ac,by simp [rootCurve],by simp [rootCurve_eq_sqrt]⟩
theorem rootLift_not_lipschitz : ¬∃ K : ℝ≥0,LipschitzOnWith K rootLift.val (Icc (0 : ℝ) 1) := by
  rintro ⟨K,hK⟩
  let u : ℝ := 1/((K : ℝ)+1)
  have hu : 0<u := by dsimp [u];positivity
  have hu1 : u≤1 := by dsimp [u];apply (div_le_one (by positivity)).mpr;linarith [K.coe_nonneg]
  have hu2 : u^2≤1 := by nlinarith
  have h := hK.dist_le_mul (u^2) ⟨sq_nonneg _,hu2⟩ 0 ⟨le_rfl,zero_le_one⟩
  change dist (rootCurve (u^2)) (rootCurve 0)≤(K : ℝ)*dist (u^2) 0 at h
  rw [rootCurve_eq_sqrt,rootCurve_eq_sqrt,Real.sqrt_sq hu.le,Real.sqrt_zero,
    Real.dist_eq,Real.dist_eq,sub_zero,sub_zero,abs_of_pos hu,abs_of_nonneg (sq_nonneg _)] at h
  have he : ((K : ℝ)+1)*u=1 := by dsimp [u];field_simp
  nlinarith [mul_pos hu hu]
theorem rootLift_period (α : Coefficient) : lineIntegral α rootLift=mean α := by
  rw [lineIntegral_eq_mean]
  change mean α*rootCurve 1=mean α
  simp [rootCurve_eq_sqrt]
end ComputationalHodge.ACLifts
