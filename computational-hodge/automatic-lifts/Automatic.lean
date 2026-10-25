module
public import Ambient
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
@[expose] public section
namespace ComputationalHodge.AutomaticLifts
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts ComputationalHodge.Dirichlet
open ComputationalHodge.UnitCircleGeometry MeasureTheory Set Complex
open scoped NNReal Topology unitInterval ComplexConjugate

theorem chord_formula (s t : ℝ) :
    ‖embed (s : CircleHodge.Circle)-embed (t : CircleHodge.Circle)‖=
      2*|Real.sin (Real.pi*(s-t))| := by
  have ht : embed (t : CircleHodge.Circle)≠0 := by
    intro h
    have hn:=embed_norm (t : CircleHodge.Circle)
    rw [h,norm_zero] at hn
    exact zero_ne_one hn
  have hd : embed (s : CircleHodge.Circle)/embed (t : CircleHodge.Circle)=
      embed ((s-t : ℝ) : CircleHodge.Circle) := by
    rw [embed_coe,embed_coe,embed_coe,circleMap_zero_div]
    congr 1
    · norm_num
    · ring
  calc
    _ = ‖embed (s : CircleHodge.Circle)/embed (t : CircleHodge.Circle)-1‖ := by
      rw [div_sub_one ht,norm_div,embed_norm,div_one]
    _ = _ := by
      rw [hd,embed_coe]
      simp only [circleMap_zero,Complex.ofReal_one,one_mul]
      rw [mul_comm _ Complex.I,Complex.norm_exp_I_mul_ofReal_sub_one]
      have ha : (2*Real.pi*(s-t))/2=Real.pi*(s-t) := by ring
      simp [ha,Real.norm_eq_abs]

/-- Quantitative local inverse estimate; no global inverse-Lipschitz claim. -/
theorem local_chord_lower (s t : ℝ) (h : |s-t|≤1/2) :
    4*|s-t|≤‖embed (s : CircleHodge.Circle)-embed (t : CircleHodge.Circle)‖ := by
  rw [chord_formula]
  have hb : |Real.pi*(s-t)|≤Real.pi/2 := by
    rw [abs_mul,abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hs:=Real.mul_abs_le_abs_sin hb
  rw [abs_mul,abs_of_pos Real.pi_pos] at hs
  have he : 2/Real.pi*(Real.pi*|s-t|)=2*|s-t| := by
    field_simp
  rw [he] at hs
  linarith

/-- Local inverse control plus compact uniform continuity transfers interval AC. -/
theorem ac_of_local_inverse {u : ℝ→ℝ} {v : ℝ→ℂ}
    (hu : UniformContinuousOn u (Icc (0 : ℝ) 1))
    (hv : AbsolutelyContinuousOnInterval v 0 1)
    (hlocal : ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (0 : ℝ) 1,
      dist (u s) (u t)<1/2 → dist (u s) (u t)≤dist (v s) (v t)) :
    AbsolutelyContinuousOnInterval u 0 1 := by
  rw [absolutelyContinuousOnInterval_iff] at hv ⊢
  intro ε hε
  obtain ⟨δ₁,hδ₁,hsmall⟩:=Metric.uniformContinuousOn_iff.mp hu (1/2) (by norm_num)
  obtain ⟨δ₂,hδ₂,hac⟩:=hv ε hε
  refine ⟨min δ₁ δ₂,lt_min hδ₁ hδ₂,?_⟩
  intro E hE hsum
  calc
    _ ≤ ∑ i∈Finset.range E.1,dist (v (E.2 i).1) (v (E.2 i).2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hend:=hE.1 i hi
      have hs : (E.2 i).1∈Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le zero_le_one] using hend.1
      have ht : (E.2 i).2∈Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le zero_le_one] using hend.2
      apply hlocal _ hs _ ht
      apply hsmall _ hs _ ht
      have hitem : dist (E.2 i).1 (E.2 i).2≤
          ∑ j∈Finset.range E.1,dist (E.2 j).1 (E.2 j).2 :=
        Finset.single_le_sum (f:=fun j : ℕ => dist (E.2 j).1 (E.2 j).2)
          (fun j _ => dist_nonneg) hi
      exact lt_of_le_of_lt hitem (lt_of_lt_of_le hsum (min_le_left _ _))
    _ < ε := hac E hE (lt_of_lt_of_le hsum (min_le_right _ _))

/-- An arbitrary complex-valued based loop with regularity and unit norm only on the interval. -/
structure AmbientLoop where
  toFun : ℝ→ℂ
  ac : AbsolutelyContinuousOnInterval toFun 0 1
  unitNorm : ∀ t∈Icc (0 : ℝ) 1,‖toFun t‖=1
  source : toFun 0=1
  target : toFun 1=1

noncomputable def circleEquiv : CircleHodge.Circle ≃ₜ _root_.Circle :=
  AddCircle.homeomorphCircle (T:=1) one_ne_zero

theorem circleEquiv_zero : circleEquiv 0=1 := by
  rw [circleEquiv,AddCircle.homeomorphCircle_apply,AddCircle.toCircle_zero]

def unitPath (F : AmbientLoop) : _root_.Path (1 : _root_.Circle) 1 where
  toFun t := ⟨F.toFun (t : ℝ),mem_sphere_zero_iff_norm.mpr (F.unitNorm t t.property)⟩
  continuous_toFun := Continuous.subtype_mk
    (F.ac.continuousOn.comp_continuous continuous_subtype_val
      (fun t => by simpa only [uIcc_of_le zero_le_one] using t.property)) _
  source' := Subtype.ext F.source
  target' := Subtype.ext F.target

noncomputable def quotientPath (F : AmbientLoop) : _root_.Path (0 : CircleHodge.Circle) 0 where
  toFun t := circleEquiv.symm (unitPath F t)
  continuous_toFun := circleEquiv.symm.continuous.comp (unitPath F).continuous
  source' := by
    apply circleEquiv.injective
    rw [Homeomorph.apply_symm_apply,Path.source,circleEquiv_zero]
  target' := by
    apply circleEquiv.injective
    rw [Homeomorph.apply_symm_apply,Path.target,circleEquiv_zero]

theorem quotientPath_embed (F : AmbientLoop) (t : unitInterval) :
    embed (quotientPath F t)=F.toFun (t : ℝ) := by
  change (AddCircle.toCircle (circleEquiv.symm (unitPath F t)) : ℂ)=_
  rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
  change (circleEquiv (circleEquiv.symm (unitPath F t)) : ℂ)=_
  rw [Homeomorph.apply_symm_apply]
  rfl

/-- Actual zero-based topological covering lift, extended by canonical clamping. -/
noncomputable def realLift (F : AmbientLoop) (t : ℝ) : ℝ :=
  circleLift (quotientPath F) (Set.projIcc 0 1 zero_le_one t)

theorem realLift_continuous (F : AmbientLoop) : Continuous (realLift F) :=
  (circleLift (quotientPath F)).continuous.comp continuous_projIcc

theorem lift_projection (F : AmbientLoop) (t : unitInterval) :
    ((circleLift (quotientPath F) t : ℝ) : CircleHodge.Circle)=quotientPath F t :=
  congrFun (circleCover.liftPath_lifts (quotientPath F).toContinuousMap 0 (by simp)) t

theorem realLift_embed (F : AmbientLoop) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    embed ((realLift F t : ℝ) : CircleHodge.Circle)=F.toFun t := by
  unfold realLift
  rw [lift_projection,quotientPath_embed,Set.projIcc_of_mem zero_le_one ht]

theorem realLift_zero (F : AmbientLoop) : realLift F 0=0 := by
  have h0 : Set.projIcc 0 1 zero_le_one (0 : ℝ)=(0 : unitInterval) := by ext; simp
  unfold realLift
  rw [h0]
  exact circleCover.liftPath_zero (quotientPath F).toContinuousMap 0 (by simp)

theorem realLift_endpoint (F : AmbientLoop) : ((realLift F 1 : ℝ) : CircleHodge.Circle)=0 := by
  apply embed_injective
  rw [realLift_embed F (by constructor <;> norm_num),F.target,embed_zero]

theorem realLift_ac (F : AmbientLoop) : AbsolutelyContinuousOnInterval (realLift F) 0 1 := by
  apply ac_of_local_inverse (isCompact_Icc.uniformContinuousOn_of_continuous
    (realLift_continuous F).continuousOn) F.ac
  intro s hs t ht hsmall
  rw [dist_eq_norm,Real.norm_eq_abs] at hsmall ⊢
  have h:=local_chord_lower (realLift F s) (realLift F t) hsmall.le
  rw [realLift_embed F hs,realLift_embed F ht] at h
  rw [dist_eq_norm]
  linarith [abs_nonneg (realLift F s-realLift F t)]

noncomputable def canonicalLift (F : AmbientLoop) : ACLift :=
  ⟨realLift F,realLift_ac F,realLift_zero F,realLift_endpoint F⟩

theorem canonical_curve (F : AmbientLoop) (t : ℝ) :
    curve (canonicalLift F) t=F.toFun (Set.projIcc 0 1 zero_le_one t) :=
  realLift_embed F (Set.projIcc 0 1 zero_le_one t).property

theorem canonical_curve_on (F : AmbientLoop) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    curve (canonicalLift F) t=F.toFun t := by
  rw [canonical_curve,Set.projIcc_of_mem zero_le_one ht]

theorem projected_canonical (F : AmbientLoop) : projectedLoop (canonicalLift F)=quotientPath F := by
  ext t
  change ((realLift F (t : ℝ) : ℝ) : CircleHodge.Circle)=_
  unfold realLift
  rw [lift_projection,Set.projIcc_of_mem zero_le_one t.property]

theorem canonical_unique_on (F : AmbientLoop) (L : ACLift)
    (h : EqOn (curve L) F.toFun (Icc (0 : ℝ) 1)) :
    EqOn L.val (canonicalLift F).val (Icc 0 1) := by
  have hp : projectedLoop L=quotientPath F := by
    ext t
    apply embed_injective
    rw [quotientPath_embed]
    exact (curve_eq_on L t.property).symm.trans (h t.property)
  intro t ht
  change L.val t=realLift F t
  rw [realLift,← hp]
  have hh:=actual_lift_on_interval L (Set.projIcc 0 1 zero_le_one t)
  simpa only [Set.projIcc_of_mem zero_le_one ht] using hh.symm

theorem embed_real_lipschitz : LipschitzWith ⟨2*Real.pi,by positivity⟩
    (fun t : ℝ => embed (t : CircleHodge.Circle)) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change dist (embed (s : CircleHodge.Circle)) (embed (t : CircleHodge.Circle))≤
    (2*Real.pi)*dist s t
  rw [dist_eq_norm,chord_formula,Real.dist_eq]
  have h:=Real.abs_sin_le_abs (x:=Real.pi*(s-t))
  rw [abs_mul,abs_of_pos Real.pi_pos] at h
  linarith

theorem curve_ac (L : ACLift) : AbsolutelyContinuousOnInterval (curve L) 0 1 := by
  have h:=embed_real_lipschitz.comp_absolutelyContinuousOnInterval L.property.1
  apply h.congr
  intro t ht
  exact (curve_eq_on L (by simpa only [uIcc_of_le zero_le_one] using ht)).symm

noncomputable def ofLift (L : ACLift) : AmbientLoop where
  toFun := curve L
  ac := curve_ac L
  unitNorm := fun t _ => curve_norm L t
  source := by simpa [curve] using (embedded_base L).1
  target := by simpa [curve] using (embedded_base L).2

theorem lift_roundtrip (L : ACLift) :
    EqOn L.val (canonicalLift (ofLift L)).val (Icc (0 : ℝ) 1) :=
  canonical_unique_on (ofLift L) L (fun _ _ => rfl)

theorem input_deriv (F : AmbientLoop) {t : ℝ} (ht : t∈Ioo (0 : ℝ) 1) :
    deriv (curve (canonicalLift F)) t=deriv F.toFun t := by
  have he : curve (canonicalLift F)=ᶠ[nhds t] F.toFun := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    exact canonical_curve_on F ⟨hx.1.le,hx.2.le⟩
  exact he.deriv_eq

theorem input_deriv_ae (F : AmbientLoop) :
    deriv (curve (canonicalLift F))=ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] deriv F.toFun := by
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc : Ioo (0 : ℝ) 1=ᵐ[volume] Ioc 0 1)]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact input_deriv F ht

noncomputable def angularValue (F : AmbientLoop) : ℝ :=
  ∫ t in (0 : ℝ)..1,angularForm (F.toFun t) (deriv F.toFun t)

def InputFiniteEnergy (F : AmbientLoop) : Prop :=
  IntervalIntegrable (fun t => ‖deriv F.toFun t‖^2) volume 0 1

noncomputable def inputEnergy (F : AmbientLoop) : ℝ :=
  ∫ t in (0 : ℝ)..1,‖deriv F.toFun t‖^2

theorem angular_integrands (F : AmbientLoop) :
    (fun t => angularForm (F.toFun t) (deriv F.toFun t))=ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun t => angularForm (curve (canonicalLift F) t) (deriv (curve (canonicalLift F)) t)) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc,input_deriv_ae F] with t ht hd
  rw [canonical_curve_on F ⟨ht.1.le,ht.2⟩,hd]

theorem angular_integrable_input (F : AmbientLoop) :
    IntervalIntegrable (fun t => angularForm (F.toFun t) (deriv F.toFun t)) volume 0 1 :=
  (angular_integrable (canonicalLift F)).congr_ae
    (by simpa only [uIoc_of_le zero_le_one] using (angular_integrands F).symm)

theorem angularValue_eq (F : AmbientLoop) : angularValue F=angularIntegral (canonicalLift F) :=
  intervalIntegral.integral_congr_ae_restrict
    (by simpa only [uIoc_of_le zero_le_one] using angular_integrands F)

theorem angular_endpoint (F : AmbientLoop) : angularValue F=realLift F 1 := by
  rw [angularValue_eq,angular_integral]
  rfl

theorem angular_winding (F : AmbientLoop) : angularValue F=winding (quotientPath F) := by
  rw [angularValue_eq,← projected_canonical,projected_winding,angular_integral]

theorem energy_integrands (F : AmbientLoop) :
    (fun t => ‖deriv F.toFun t‖^2)=ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun t => ‖deriv (curve (canonicalLift F)) t‖^2) :=
  (input_deriv_ae F).symm.fun_comp (fun z : ℂ => ‖z‖^2)

theorem finite_energy_input_iff (F : AmbientLoop) : InputFiniteEnergy F↔FiniteEnergy (canonicalLift F) := by
  have h : InputFiniteEnergy F↔AmbientFiniteEnergy (canonicalLift F) :=
    intervalIntegrable_congr_ae
      (by simpa only [uIoc_of_le zero_le_one] using energy_integrands F)
  exact h.trans (finite_energy_iff (canonicalLift F))

theorem input_energy_eq (F : AmbientLoop) : inputEnergy F=ambientEnergy (canonicalLift F) :=
  intervalIntegral.integral_congr_ae_restrict
    (by simpa only [uIoc_of_le zero_le_one] using energy_integrands F)

theorem input_energy_lift (F : AmbientLoop) : inputEnergy F=(2*Real.pi)^2*energy (canonicalLift F) := by
  rw [input_energy_eq,ambient_energy]

theorem input_class_minimum (F G : AmbientLoop) (h : InputFiniteEnergy G)
    (hm : _root_.Path.Homotopic (quotientPath F) (quotientPath G)) :
    ambientEnergy (affine (canonicalLift F)) ≤ inputEnergy G := by
  rw [input_energy_eq]
  apply ambient_class_minimum
  · exact (finite_energy_iff _).mpr ((finite_energy_input_iff G).mp h)
  · simpa only [projected_canonical] using hm

theorem input_minimum_rigid (F : AmbientLoop) (h : InputFiniteEnergy F) :
    inputEnergy F=(2*Real.pi)^2*(angularValue F)^2 ↔
      curve (canonicalLift F)=curve (affine (canonicalLift F)) := by
  rw [input_energy_eq,angular_endpoint]
  exact ambient_minimum_rigid (canonicalLift F)
    ((finite_energy_iff _).mpr ((finite_energy_input_iff F).mp h))

theorem integer_endpoint (F : AmbientLoop) : ∃ n : ℤ,(n : ℝ)=realLift F 1 := by
  obtain ⟨n,hn⟩:=(AddCircle.coe_eq_zero_iff (p:=(1 : ℝ))).mp (realLift_endpoint F)
  exact ⟨n,by simpa using hn⟩

def repeatTrace : ℕ→Trace 0 0
  | 0 => .refl 0
  | n+1 => .trans unitTrace (repeatTrace n)

theorem count_repeat (n : ℕ) : count (repeatTrace n)=(n : ℤ) := by
  induction n with
  | zero => rfl
  | succ n hn => simp [repeatTrace,count,unitTrace,hn];omega

def integerTrace : ℤ→Trace 0 0
  | .ofNat n => repeatTrace n
  | .negSucc n => .symm (repeatTrace (n+1))

theorem count_integerTrace (n : ℤ) : count (integerTrace n)=n := by
  cases n with
  | ofNat n => exact count_repeat n
  | negSucc n => simp [integerTrace,count,count_repeat,Int.negSucc_eq]

/-- A finite computational representative chosen from the derived integral endpoint. -/
noncomputable def normalTrace (F : AmbientLoop) : Trace 0 0 :=
  integerTrace (integer_endpoint F).choose

theorem normalTrace_count (F : AmbientLoop) : (count (normalTrace F) : ℝ)=realLift F 1 := by
  rw [normalTrace,count_integerTrace]
  exact (integer_endpoint F).choose_spec

theorem representative_endpoint (F : AmbientLoop) :
    (fromTrace (normalTrace F)).val 1=(canonicalLift F).val 1 := by
  change actualLift (normalTrace F) 1=realLift F 1
  rw [actualLift_eq_rawLift,rawLift_one]
  exact normalTrace_count F

/-- This homotopy is in the actual additive circle, not the whole complex plane. -/
theorem representative_homotopic (F : AmbientLoop) :
    _root_.Path.Homotopic (quotientPath F) (GeometricTrace.realize (normalTrace F)) := by
  rw [← projected_canonical,← projected_fromTrace]
  have ha : affine (canonicalLift F)=affine (fromTrace (normalTrace F)) := by
    apply Subtype.ext
    funext t
    change (canonicalLift F).val 1*t=(fromTrace (normalTrace F)).val 1*t
    rw [representative_endpoint]
  have h:=affine_homotopic (canonicalLift F)
  rw [ha] at h
  exact h.trans (affine_homotopic (fromTrace (normalTrace F))).symm

theorem angular_representative (F : AmbientLoop) :
    angularValue F=period (normalTrace F) unitCochain := by
  rw [angular_endpoint,period_unit_count]
  exact (normalTrace_count F).symm

theorem harmonic_representative (F : AmbientLoop) (α : Coefficient) :
    mean α*angularValue F=period (normalTrace F) (meanHarmonic α) := by
  rw [angular_representative,period_unit_count]
  exact (period_mean_count α (normalTrace F)).symm

theorem minimum_representative (F : AmbientLoop) :
    ambientEnergy (affine (canonicalLift F))=
      (2*Real.pi)^2*(period (normalTrace F) unitCochain)^2 := by
  rw [ambient_energy,affine_energy]
  change (2*Real.pi)^2*(realLift F 1)^2=_
  rw [← angular_endpoint,angular_representative]

theorem ofLift_angular (L : ACLift) : angularValue (ofLift L)=angularIntegral L := rfl
theorem ofLift_energy (L : ACLift) : inputEnergy (ofLift L)=ambientEnergy L := rfl

noncomputable def ofTrace (p : Trace 0 0) : AmbientLoop := ofLift (fromTrace p)

theorem raw_input_period (p : Trace 0 0) : angularValue (ofTrace p)=period p unitCochain :=
  angular_computational p

theorem raw_input_finite (p : Trace 0 0) : InputFiniteEnergy (ofTrace p) := raw_finite_energy p

theorem raw_lift_roundtrip (p : Trace 0 0) :
    EqOn (fromTrace p).val (canonicalLift (ofTrace p)).val (Icc (0 : ℝ) 1) :=
  lift_roundtrip (fromTrace p)

end ComputationalHodge.AutomaticLifts
