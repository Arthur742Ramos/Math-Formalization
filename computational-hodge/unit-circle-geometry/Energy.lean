module
public import TraceFoundation
@[expose] public section
namespace ComputationalHodge.Dirichlet
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts
open MeasureTheory Set
open scoped NNReal Topology unitInterval
/-- Finite squared-speed energy is required; totalized integrals alone do not assert finiteness. -/
def FiniteEnergy (L : ACLift) : Prop :=
  IntervalIntegrable (fun t => (deriv L.val t)^2) volume 0 1
noncomputable def energy (L : ACLift) : ℝ := ∫ t in (0 : ℝ)..1,(deriv L.val t)^2
noncomputable def defect (L : ACLift) : ℝ := ∫ t in (0 : ℝ)..1,(deriv L.val t-L.val 1)^2
theorem derivative_integral (L : ACLift) :
    ∫ t in (0 : ℝ)..1,deriv L.val t=L.val 1 := by
  simpa [L.property.2.1] using L.property.1.integral_deriv_eq_sub
theorem defect_integrable (L : ACLift) (h : FiniteEnergy L) :
    IntervalIntegrable (fun t => (deriv L.val t-L.val 1)^2) volume 0 1 := by
  convert (h.sub (L.property.1.intervalIntegrable_deriv.const_mul (2*L.val 1))).add
    (intervalIntegrable_const (c := (L.val 1)^2)) using 1
  ext t
  ring
theorem energy_splitting (L : ACLift) (h : FiniteEnergy L) :
    energy L=(L.val 1)^2+defect L := by
  have he : (fun t => (deriv L.val t-L.val 1)^2)=
      fun t => (deriv L.val t)^2-(2*L.val 1)*deriv L.val t+(L.val 1)^2 := by
    funext t;ring
  unfold defect
  rw [he,intervalIntegral.integral_add
    (h.sub (L.property.1.intervalIntegrable_deriv.const_mul _)) intervalIntegrable_const,
    intervalIntegral.integral_sub h (L.property.1.intervalIntegrable_deriv.const_mul _),
    intervalIntegral.integral_const_mul,derivative_integral]
  simp only [intervalIntegral.integral_const,sub_zero,one_smul]
  unfold energy;ring
theorem energy_lower_bound (L : ACLift) (h : FiniteEnergy L) : (L.val 1)^2≤energy L := by
  rw [energy_splitting L h]
  exact le_add_of_nonneg_right (intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _))
theorem minimum_implies_affine (L : ACLift) (h : FiniteEnergy L)
    (he : energy L=(L.val 1)^2) : ∀ t∈Icc (0 : ℝ) 1,L.val t=L.val 1*t := by
  have hd : defect L=0 := by have hs := energy_splitting L h;rw [he] at hs;linarith only [hs]
  have hz := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae zero_le_one
    (Filter.Eventually.of_forall (fun t => sq_nonneg (deriv L.val t-L.val 1)))
    (defect_integrable L h)).mp hd
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hz
  have hg : ∀ᵐ t : ℝ,t∈uIcc (0 : ℝ) 1 → deriv L.val t=L.val 1 := by
    rw [uIcc_of_le zero_le_one]
    apply (ae_restrict_iff' measurableSet_Icc).mp
    filter_upwards [hz] with t ht
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp ht)
  have hac : AbsolutelyContinuousOnInterval (fun t => L.val t-L.val 1*t) 0 1 :=
    L.property.1.fun_sub
      ((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval.const_mul (L.val 1))
  have hh : ∀ᵐ t : ℝ,t∈uIcc (0 : ℝ) 1 → HasDerivAt (fun x => L.val x-L.val 1*x) 0 t := by
    filter_upwards [L.property.1.ae_differentiableAt,hg] with t ht hd hm
    simpa only [id_eq,mul_one,hd hm,sub_self] using (ht hm).hasDerivAt.fun_sub ((hasDerivAt_id t).const_mul (L.val 1))
  obtain ⟨C,hC⟩ := hac.const_of_ae_hasDerivAt_zero hh
  have hc : C=0 := by simpa [L.property.2.1] using (hC 0 (by norm_num [uIcc_of_le zero_le_one])).symm
  intro t ht
  have hp := hC t (by simpa [uIcc_of_le zero_le_one] using ht)
  rw [hc] at hp
  exact sub_eq_zero.mp hp
noncomputable def affine (L : ACLift) : ACLift :=
  ⟨fun t => L.val 1*t,
    (LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval.const_mul (L.val 1),
    by simp,by simpa using L.property.2.2⟩
theorem affine_deriv (L : ACLift) (t : ℝ) : deriv (affine L).val t=L.val 1 := by
  simpa only [affine,id_eq,mul_one] using ((hasDerivAt_id t).const_mul (L.val 1)).deriv
theorem affine_finite (L : ACLift) : FiniteEnergy (affine L) := by
  simpa only [FiniteEnergy,affine_deriv] using
    (intervalIntegrable_const (c := (L.val 1)^2) : IntervalIntegrable _ volume 0 1)
theorem affine_energy (L : ACLift) : energy (affine L)=(L.val 1)^2 := by
  simp [energy,affine_deriv]
theorem energy_congr_on {L M : ACLift} (h : EqOn L.val M.val (Icc 0 1)) :
    energy L=energy M := by
  apply intervalIntegral.integral_congr_uIoo
  intro t ht
  have ht' : t∈Ioo (0 : ℝ) 1 := by simpa [uIoo_of_lt zero_lt_one] using ht
  have he : L.val=ᶠ[nhds t] M.val := by
    filter_upwards [Ioo_mem_nhds ht'.1 ht'.2] with x hx
    exact h ⟨hx.1.le,hx.2.le⟩
  exact congrArg (fun x : ℝ => x^2) he.deriv_eq
theorem minimum_iff_affine (L : ACLift) (h : FiniteEnergy L) :
    energy L=(L.val 1)^2 ↔ EqOn L.val (affine L).val (Icc 0 1) := by
  constructor
  · exact minimum_implies_affine L h
  · intro he;rw [energy_congr_on he,affine_energy]
/-- Actual endpoint-fixed homotopy obtained by linear interpolation of the real lifts. -/
noncomputable def affineHomotopy (L : ACLift) :
    _root_.Path.Homotopy (projectedLoop L) (projectedLoop (affine L)) where
  toFun st := (((1-(st.1 : ℝ))*L.val (st.2 : ℝ)+(st.1 : ℝ)*(L.val 1*(st.2 : ℝ)) : ℝ) : CircleHodge.Circle)
  continuous_toFun := by
    apply (AddCircle.continuous_mk' (1 : ℝ)).comp
    have hc : Continuous (fun st : unitInterval×unitInterval => L.val (st.2 : ℝ)) :=
      L.property.1.continuousOn.comp_continuous
        (continuous_subtype_val.comp continuous_snd)
        (fun st => by simpa only [uIcc_of_le zero_le_one] using st.2.property)
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul hc).add
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_const.mul (continuous_subtype_val.comp continuous_snd)))
  map_zero_left := by intro t;simp [projectedLoop]
  map_one_left := by intro t;simp [projectedLoop,affine]
  prop' := by
    intro s t ht
    rcases ht with ht|ht
    · subst t;simp [projectedLoop,L.property.2.1]
    · have ht' : t=1 := by simpa using ht
      subst t
      change (((1-(s : ℝ))*L.val 1+(s : ℝ)*(L.val 1*1) : ℝ) : CircleHodge.Circle)=((L.val 1 : ℝ) : CircleHodge.Circle)
      congr 1;ring
theorem affine_homotopic (L : ACLift) :
    _root_.Path.Homotopic (projectedLoop L) (projectedLoop (affine L)) := ⟨affineHomotopy L⟩
theorem class_minimum (L M : ACLift) (h : FiniteEnergy M)
    (hm : _root_.Path.Homotopic (projectedLoop L) (projectedLoop M)) :
    energy (affine L)≤energy M := by
  have he : L.val 1=M.val 1 := by
    rw [← projected_winding,← projected_winding];exact winding_homotopic hm
  rw [affine_energy,he];exact energy_lower_bound M h
theorem fromTrace_finite (p : Trace 0 0) : FiniteEnergy (fromTrace p) := by
  obtain ⟨K,hK⟩ := rawLift_lipschitz p
  rw [← actualLift_eq_rawLift] at hK
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr
  apply IntegrableOn.of_bound (measure_Icc_lt_top)
    ((aestronglyMeasurable_deriv (actualLift p) _).pow 2) ((K : ℝ)^2)
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hn := norm_deriv_le_of_lipschitz (x₀ := t) hK
  change (deriv (actualLift p) t)^2≤(K : ℝ)^2
  simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hn 2
def paused : Trace 0 0 := .trans unitTrace (.refl 0)
theorem paused_endpoint : (fromTrace paused).val 1=1 := by
  change actualLift paused 1=1
  rw [actualLift_eq_rawLift,rawLift_one];norm_num [paused,unitTrace,count]
theorem paused_not_affine : ¬EqOn (fromTrace paused).val (affine (fromTrace paused)).val (Icc 0 1) := by
  intro h
  have hh := h (x := (1/2 : ℝ)) (by norm_num)
  change actualLift paused (1/2)=(fromTrace paused).val 1*(1/2) at hh
  rw [paused_endpoint,actualLift_eq_rawLift] at hh
  norm_num [paused,unitTrace,rawLift,clamp] at hh
theorem paused_energy_strict : 1<energy (fromTrace paused) := by
  have hl := energy_lower_bound (fromTrace paused) (fromTrace_finite paused)
  have hn : energy (fromTrace paused)≠1 := by
    intro he
    apply paused_not_affine
    apply (minimum_iff_affine _ (fromTrace_finite paused)).mp
    simpa [paused_endpoint] using he
  rw [paused_endpoint] at hl
  norm_num at hl
  exact lt_of_le_of_ne hl (Ne.symm hn)
theorem computational_minimum (p : Trace 0 0) :
    energy (affine (fromTrace p))=(period p unitCochain)^2 := by
  rw [affine_energy,period_unit_count]
  change (actualLift p 1)^2=(count p : ℝ)^2
  rw [actualLift_eq_rawLift,rawLift_one]
end ComputationalHodge.Dirichlet
