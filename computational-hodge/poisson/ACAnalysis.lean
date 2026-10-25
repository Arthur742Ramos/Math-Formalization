module
public import CirclePeriods
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
@[expose] public section
namespace ComputationalHodge.ACLifts
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge
open ComputationalHodge.TraceIntegrals
open MeasureTheory Set
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
theorem actual_lift_on_interval (L : ACLift) (t : unitInterval) :
    circleLift (projectedLoop L) t=L.val (t : ℝ) := by
  let F : C(unitInterval,ℝ) := ⟨fun t => L.val (t : ℝ),
    L.property.1.continuousOn.comp_continuous continuous_subtype_val
      (fun _ => by simp)⟩
  have h : F=circleLift (projectedLoop L) := by
    apply (circleCover.eq_liftPath_iff' _).mpr
    exact ⟨rfl,L.property.2.1⟩
  exact (congrArg (fun f : C(unitInterval,ℝ) => f t) h).symm
theorem projected_winding (L : ACLift) : winding (projectedLoop L)=L.val 1 :=
  actual_lift_on_interval L 1
/-- Clamped actual covering lift; no equality with L outside the interval is asserted. -/
noncomputable def coveringLift (L : ACLift) (t : ℝ) : ℝ :=
  circleLift (projectedLoop L) (Set.projIcc 0 1 zero_le_one t)
theorem coveringLift_eq_on (L : ACLift) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    coveringLift L t=L.val t := by
  simp only [coveringLift,actual_lift_on_interval,Set.projIcc_of_mem zero_le_one ht]
theorem coveringLift_deriv (L : ACLift) {t : ℝ} (ht : t∈Ioo (0 : ℝ) 1) :
    deriv (coveringLift L) t=deriv L.val t := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
  exact coveringLift_eq_on L ⟨hx.1.le,hx.2.le⟩
/-- Ordinary integration on this actual projected curve, against its real-lift derivative. -/
noncomputable def lineIntegral (α : Coefficient) (L : ACLift) : ℝ :=
  ∫ t in (0 : ℝ)..1,α (projectedLoop L (Set.projIcc 0 1 zero_le_one t))*deriv L.val t
theorem lineIntegral_eq_actual (α : Coefficient) (L : ACLift) :
    lineIntegral α L=∫ t in (0 : ℝ)..1,
      α (projectedLoop L (Set.projIcc 0 1 zero_le_one t))*deriv (coveringLift L) t := by
  apply intervalIntegral.integral_congr_uIoo
  intro t ht
  exact congrArg (fun x : ℝ => α (projectedLoop L (Set.projIcc 0 1 zero_le_one t))*x)
    (coveringLift_deriv L (by simpa [uIoo_of_lt zero_lt_one] using ht)).symm
noncomputable def primitive (α : Coefficient) (u : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..u,cover α x
theorem primitive_hasDerivAt (α : Coefficient) (x : ℝ) :
    HasDerivAt (primitive α) (cover α x) x :=
  intervalIntegral.integral_hasDerivAt_right ((cover_continuous α).intervalIntegrable 0 x)
    (cover_continuous α).aestronglyMeasurable.stronglyMeasurableAtFilter
    (cover_continuous α).continuousAt
theorem primitive_lipschitz (α : Coefficient) : ∃ K : ℝ≥0,LipschitzWith K (primitive α) := by
  obtain ⟨C,hC⟩ := (isCompact_range α.continuous).isBounded.exists_norm_le
  have h0 : 0≤C := (norm_nonneg (α 0)).trans (hC _ ⟨0,rfl⟩)
  refine ⟨⟨C,h0⟩,lipschitzWith_of_nnnorm_deriv_le
    (fun x => (primitive_hasDerivAt α x).differentiableAt) (fun x => ?_)⟩
  rw [(primitive_hasDerivAt α x).deriv]
  exact hC _ ⟨(x : CircleHodge.Circle),rfl⟩
theorem primitive_comp_ac (α : Coefficient) (L : ACLift) :
    AbsolutelyContinuousOnInterval (fun t => primitive α (L.val t)) 0 1 := by
  obtain ⟨K,hK⟩ := primitive_lipschitz α
  exact hK.comp_absolutelyContinuousOnInterval L.property.1
theorem chain_rule_ae (α : Coefficient) (L : ACLift) :
    ∀ᵐ t : ℝ, t∈uIcc (0 : ℝ) 1 →
      deriv (fun x => primitive α (L.val x)) t=cover α (L.val t)*deriv L.val t := by
  filter_upwards [L.property.1.ae_differentiableAt] with t ht hmem
  exact ((primitive_hasDerivAt α (L.val t)).comp t (ht hmem).hasDerivAt).deriv
theorem cover_integrand_integrable (α : Coefficient) (L : ACLift) :
    IntervalIntegrable (fun t => cover α (L.val t)*deriv L.val t) volume 0 1 := by
  apply (primitive_comp_ac α L).intervalIntegrable_deriv.congr_ae
  exact (ae_restrict_mem measurableSet_uIoc).and (ae_restrict_of_ae (chain_rule_ae α L)) |>.mono
    (fun t ht => ht.2 (uIoc_subset_uIcc ht.1))
theorem lineIntegral_eq_cover (α : Coefficient) (L : ACLift) :
    lineIntegral α L=∫ t in (0 : ℝ)..1,cover α (L.val t)*deriv L.val t := by
  apply intervalIntegral.integral_congr
  intro t ht
  have h : t∈Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
  simp only [projectedLoop,cover,Set.projIcc_of_mem zero_le_one h,Path.coe_mk_mk]
theorem line_integrand_integrable (α : Coefficient) (L : ACLift) :
    IntervalIntegrable
      (fun t => α (projectedLoop L (Set.projIcc 0 1 zero_le_one t))*deriv L.val t) volume 0 1 := by
  apply (cover_integrand_integrable α L).congr
  intro t ht
  have h : t∈Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using (uIoc_subset_uIcc ht)
  simp only [projectedLoop,cover,Set.projIcc_of_mem zero_le_one h,Path.coe_mk_mk]
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
theorem lineIntegral_homotopic (α : Coefficient) (L M : ACLift)
    (h : _root_.Path.Homotopic (projectedLoop L) (projectedLoop M)) :
    lineIntegral α L=lineIntegral α M := by
  rw [lineIntegral_eq_mean,lineIntegral_eq_mean,← projected_winding,← projected_winding,
    winding_homotopic h]
end ComputationalHodge.ACLifts
