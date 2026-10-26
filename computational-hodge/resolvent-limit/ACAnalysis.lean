module
public import CirclePeriods
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
@[expose] public section
namespace ComputationalHodge.ACLifts
open ComputationalPaths.Path.GeometricTopology ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge ComputationalHodge.TraceIntegrals MeasureTheory Set
open scoped NNReal Topology unitInterval
/-- A real lift with regularity only on the interval, not a presumed period formula. -/
abbrev ACLift := {f : ℝ → ℝ // AbsolutelyContinuousOnInterval f 0 1 ∧
  f 0=0 ∧ ((f 1 : ℝ) : CircleHodge.Circle)=0}
def projectedLoop (L : ACLift) : _root_.Path (0 : CircleHodge.Circle) 0 where
  toFun t := ((L.val (t : ℝ) : ℝ) : CircleHodge.Circle)
  continuous_toFun := by
    apply (AddCircle.continuous_mk' (1 : ℝ)).comp
    exact L.property.1.continuousOn.comp_continuous continuous_subtype_val
      (fun _ => by simp)
  source' := by simpa using congrArg (fun x : ℝ => (x : CircleHodge.Circle)) L.property.2.1
  target' := L.property.2.2
/-- Ordinary integration on this actual projected curve, against its real-lift derivative. -/
noncomputable def lineIntegral (α : Coefficient) (L : ACLift) : ℝ :=
  ∫ t in (0 : ℝ)..1,α (projectedLoop L (Set.projIcc 0 1 zero_le_one t))*deriv L.val t
noncomputable def primitive (α : Coefficient) (u : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..u,cover α x
theorem primitive_hasDerivAt (α : Coefficient) (x : ℝ) :
    HasDerivAt (primitive α) (cover α x) x :=
  intervalIntegral.integral_hasDerivAt_right ((cover_continuous α).intervalIntegrable 0 x)
    (cover_continuous α).aestronglyMeasurable.stronglyMeasurableAtFilter
    (cover_continuous α).continuousAt
theorem primitive_lipschitz (α : Coefficient) : ∃ K : ℝ≥0,LipschitzWith K (primitive α) := ⟨‖α‖₊,lipschitzWith_of_nnnorm_deriv_le
    (fun x => (primitive_hasDerivAt α x).differentiableAt)
    (fun x => by rw [(primitive_hasDerivAt α x).deriv];exact NNReal.coe_le_coe.mp (α.norm_coe_le_norm (x : CircleHodge.Circle)))⟩

theorem primitive_comp_ac (α : Coefficient) (L : ACLift) :
    AbsolutelyContinuousOnInterval (fun t => primitive α (L.val t)) 0 1 := (primitive_lipschitz α).choose_spec.comp_absolutelyContinuousOnInterval L.property.1
theorem chain_rule_ae (α : Coefficient) (L : ACLift) :
    ∀ᵐ t : ℝ, t∈uIcc (0 : ℝ) 1 →
      deriv (fun x => primitive α (L.val x)) t=cover α (L.val t)*deriv L.val t := by
  filter_upwards [L.property.1.ae_differentiableAt] with t ht hmem
  exact ((primitive_hasDerivAt α (L.val t)).comp t (ht hmem).hasDerivAt).deriv
theorem cover_integrand_integrable (α : Coefficient) (L : ACLift) :
    IntervalIntegrable (fun t => cover α (L.val t)*deriv L.val t) volume 0 1 := (primitive_comp_ac α L).intervalIntegrable_deriv.congr_ae
    (((ae_restrict_mem measurableSet_uIoc).and (ae_restrict_of_ae (chain_rule_ae α L))).mono
      (fun _t ht => ht.2 (uIoc_subset_uIcc ht.1)))
theorem lineIntegral_eq_cover (α : Coefficient) (L : ACLift) :
    lineIntegral α L=∫ t in (0 : ℝ)..1,cover α (L.val t)*deriv L.val t := intervalIntegral.integral_congr (fun t ht =>
    congrArg (fun s : Icc (0 : ℝ) 1 => α (projectedLoop L s)*deriv L.val t)
      (Set.projIcc_of_mem zero_le_one (by simpa only [uIcc_of_le zero_le_one] using ht)))
theorem line_integrand_integrable (α : Coefficient) (L : ACLift) :
    IntervalIntegrable
      (fun t => α (projectedLoop L (Set.projIcc 0 1 zero_le_one t))*deriv L.val t) volume 0 1 := (cover_integrand_integrable α L).congr (fun t ht =>
    (congrArg (fun s : Icc (0 : ℝ) 1 => α (projectedLoop L s)*deriv L.val t)
      (Set.projIcc_of_mem zero_le_one (by simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ht))).symm)
theorem lineIntegral_eq_endpoint (α : Coefficient) (L : ACLift) :
    lineIntegral α L=∫ x in (0 : ℝ)..L.val 1,cover α x := by
  rw [lineIntegral_eq_cover]
  calc
    _ = ∫ t in (0 : ℝ)..1,deriv (fun x => primitive α (L.val x)) t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [chain_rule_ae α L] with t ht hmem
      exact (ht (uIoc_subset_uIcc hmem)).symm
    _ = _ := by simpa [primitive,L.property.2.1] using (primitive_comp_ac α L).integral_deriv_eq_sub
theorem endpoint_integral (L : ACLift) : ∃ n : ℤ,(n : ℝ)=L.val 1 := by
  obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp L.property.2.2
  exact ⟨n,by simpa using hn⟩
theorem lineIntegral_eq_mean (α : Coefficient) (L : ACLift) :
    lineIntegral α L=mean α*L.val 1 := by
  obtain ⟨n,hn⟩ := endpoint_integral L
  rw [lineIntegral_eq_endpoint,← hn]
  have h := (cover_periodic α).intervalIntegral_add_zsmul_eq n 0
    (fun a b => (cover_continuous α).intervalIntegrable a b)
  simpa [mean,mul_comm] using h
end ComputationalHodge.ACLifts
