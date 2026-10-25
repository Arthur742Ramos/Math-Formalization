module
public import Potential
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Measure.OpenPos
@[expose] public section
namespace ComputationalHodge.MetricHodge
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.LoopCharacters
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts
open MeasureTheory Set
open scoped Topology NNReal

/-- Positive continuous length density. The coordinate convention is ds=ρ dx. -/
abbrev Density := {ρ : Coefficient // ∀ q,0<ρ q}
theorem density_ne (ρ : Density) (q : CircleHodge.Circle) : ρ.val q≠0 :=
  ne_of_gt (ρ.property q)
theorem continuous_integrable {f : CircleHodge.Circle→ℝ} (h : Continuous f) :
    Integrable f volume := h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
theorem mean_circle (α : Coefficient) : mean α=∫ q : CircleHodge.Circle,α q := by
  simpa [mean,cover] using (UnitAddCircle.intervalIntegral_preimage 0 α)
theorem mean_pos (ρ : Density) : 0<mean ρ.val := by
  rw [mean_circle]
  exact integral_pos_of_integrable_nonneg_nonzero ρ.val.continuous
    (continuous_integrable ρ.val.continuous) (fun q => (ρ.property q).le) (density_ne ρ 0)
theorem mean_smul (c : ℝ) (α : Coefficient) : mean (c•α)=c*mean α := by
  simp only [mean_circle,ContinuousMap.smul_apply,smul_eq_mul]
  exact integral_const_mul c _

/-- Coordinate star from one-form coefficients to scalar coefficients. -/
noncomputable def starOne (ρ : Density) (α : Coefficient) : Coefficient where
  toFun q := α q/ρ.val q
  continuous_toFun := α.continuous.div ρ.val.continuous (density_ne ρ)
/-- Coordinate star from scalar coefficients to one-form coefficients. -/
noncomputable def starZero (ρ : Density) (φ : Coefficient) : Coefficient := φ*ρ.val
theorem starZero_starOne (ρ : Density) (α : Coefficient) :
    starZero ρ (starOne ρ α)=α := by
  ext q
  exact div_mul_cancel₀ _ (density_ne ρ q)
theorem starOne_starZero (ρ : Density) (φ : Coefficient) :
    starOne ρ (starZero ρ φ)=φ := by
  ext q
  exact mul_div_cancel_right₀ _ (density_ne ρ q)
/-- Degree-correct coordinate expression -starOne d starOne; output need not be continuous. -/
noncomputable def codifferential (ρ : Density) (α : Coefficient) (x : ℝ) : ℝ :=
  -(deriv (cover (starOne ρ α)) x)/cover ρ.val x
/-- Differentiability guards the totalized derivative. -/
def MetricHarmonic (ρ : Density) (α : Coefficient) : Prop :=
  Differentiable ℝ (cover (starOne ρ α)) ∧ ∀ x,codifferential ρ α x=0
theorem harmonic_iff_multiple (ρ : Density) (α : Coefficient) :
    MetricHarmonic ρ α ↔ ∃ c : ℝ,α=c•ρ.val := by
  constructor
  · rintro ⟨hd,hzero⟩
    have hz (x : ℝ) : deriv (cover (starOne ρ α)) x=0 := by
      have h:=hzero x
      exact neg_eq_zero.mp ((div_eq_zero_iff.mp h).resolve_right (density_ne ρ (x : CircleHodge.Circle)))
    refine ⟨cover (starOne ρ α) 0,?_⟩
    ext q
    induction q using Quotient.inductionOn with | _ x =>
    have h:=is_const_of_deriv_eq_zero hd hz x 0
    change α (x : CircleHodge.Circle)/ρ.val (x : CircleHodge.Circle)=_ at h
    exact (div_eq_iff (density_ne ρ (x : CircleHodge.Circle))).mp h
  · rintro ⟨c,rfl⟩
    have he : cover (starOne ρ (c•ρ.val))=fun _ => c := by
      funext x
      exact mul_div_cancel_right₀ c (density_ne ρ (x : CircleHodge.Circle))
    refine ⟨by rw [he];exact differentiable_const c,?_⟩
    intro x
    simp [codifferential,he]
noncomputable def representative (ρ : Density) (α : Coefficient) : Coefficient :=
  (mean α/mean ρ.val)•ρ.val
theorem representative_harmonic (ρ : Density) (α : Coefficient) :
    MetricHarmonic ρ (representative ρ α) :=
  (harmonic_iff_multiple ρ _).mpr ⟨_,rfl⟩
theorem representative_mean (ρ : Density) (α : Coefficient) :
    mean (representative ρ α)=mean α := by
  rw [representative,mean_smul]
  exact div_mul_cancel₀ _ (ne_of_gt (mean_pos ρ))
theorem representative_exact (ρ : Density) (α : Coefficient) :
    ExactCoefficient (α-representative ρ α) := by
  apply (mean_zero_iff_exact _).mp
  rw [mean_sub,representative_mean,sub_self]
theorem representative_potential (ρ : Density) (α : Coefficient) :
    ∃ F : Coefficient,ContDiff ℝ 1 (cover F) ∧ F 0=0 ∧
      ∀ x,deriv (cover F) x=cover (α-representative ρ α) x := by
  refine ⟨potential (α-representative ρ α),potential_contDiff _,potential_zero _,?_⟩
  have hm : mean (α-representative ρ α)=0 := by rw [mean_sub,representative_mean,sub_self]
  intro x
  simpa [hm] using potential_deriv (α-representative ρ α) x
theorem unique_harmonic_representative (ρ : Density) (α : Coefficient) :
    ∃! h : Coefficient,MetricHarmonic ρ h ∧ ExactCoefficient (α-h) := by
  refine ⟨representative ρ α,⟨representative_harmonic ρ α,representative_exact ρ α⟩,?_⟩
  rintro h ⟨hh,he⟩
  obtain ⟨c,rfl⟩:=(harmonic_iff_multiple ρ h).mp hh
  have hz:=exact_mean_zero he
  rw [mean_sub,mean_smul] at hz
  have hc : c=mean α/mean ρ.val := by
    apply (eq_div_iff (ne_of_gt (mean_pos ρ))).mpr
    exact (sub_eq_zero.mp hz).symm
  rw [hc]
  rfl

/-- Ordinary one-form L2 energy for ds=ρ dx, not path-velocity energy. -/
noncomputable def weightedEnergy (ρ : Density) (α : Coefficient) : ℝ :=
  ∫ q : CircleHodge.Circle,(α q)^2/ρ.val q
noncomputable def weightedPairing (ρ : Density) (α β : Coefficient) : ℝ :=
  ∫ q : CircleHodge.Circle,α q*β q/ρ.val q
theorem energy_integrand_continuous (ρ : Density) (α : Coefficient) :
    Continuous (fun q => (α q)^2/ρ.val q) :=
  (α.continuous.pow 2).div ρ.val.continuous (density_ne ρ)
theorem energy_integrable (ρ : Density) (α : Coefficient) :
    Integrable (fun q => (α q)^2/ρ.val q) volume :=
  continuous_integrable (energy_integrand_continuous ρ α)
theorem pairing_integrable (ρ : Density) (α β : Coefficient) :
    Integrable (fun q => α q*β q/ρ.val q) volume :=
  continuous_integrable ((α.continuous.mul β.continuous).div ρ.val.continuous (density_ne ρ))
theorem energy_interval (ρ : Density) (α : Coefficient) :
    weightedEnergy ρ α=∫ x in (0 : ℝ)..1,(cover α x)^2/cover ρ.val x := by
  simpa [weightedEnergy,cover] using
    (UnitAddCircle.intervalIntegral_preimage 0 (fun q => (α q)^2/ρ.val q)).symm
theorem energy_nonneg (ρ : Density) (α : Coefficient) : 0≤weightedEnergy ρ α :=
  integral_nonneg (fun q => div_nonneg (sq_nonneg _) (ρ.property q).le)
theorem energy_zero_iff (ρ : Density) (α : Coefficient) : weightedEnergy ρ α=0 ↔ α=0 := by
  constructor
  · intro h
    have hae:= (integral_eq_zero_iff_of_nonneg
      (fun q => div_nonneg (sq_nonneg (α q)) (ρ.property q).le) (energy_integrable ρ α)).mp h
    have he:=((energy_integrand_continuous ρ α).ae_eq_iff_eq volume continuous_const).mp hae
    ext q
    have hq:=congrFun he q
    exact sq_eq_zero_iff.mp ((div_eq_zero_iff.mp hq).resolve_right (density_ne ρ q))
  · rintro rfl
    simp [weightedEnergy]
theorem representative_orthogonal (ρ : Density) (α : Coefficient) :
    weightedPairing ρ (representative ρ α) (α-representative ρ α)=0 := by
  have he : (fun q => representative ρ α q*(α-representative ρ α) q/ρ.val q)=
      fun q => (mean α/mean ρ.val)*(α-representative ρ α) q := by
    funext q
    change ((mean α/mean ρ.val)*ρ.val q)*_ /ρ.val q=_
    field_simp [density_ne ρ q,ne_of_gt (mean_pos ρ)]
  unfold weightedPairing
  rw [he,integral_const_mul,← mean_circle,exact_mean_zero (representative_exact ρ α),mul_zero]
theorem energy_add (ρ : Density) (α β : Coefficient) :
    weightedEnergy ρ (α+β)=weightedEnergy ρ α+weightedEnergy ρ β+2*weightedPairing ρ α β := by
  have he : (fun q => ((α+β) q)^2/ρ.val q)=
      fun q => (α q)^2/ρ.val q+(β q)^2/ρ.val q+2*(α q*β q/ρ.val q) := by
    funext q
    change (α q+β q)^2/ρ.val q=_
    ring
  unfold weightedEnergy weightedPairing
  rw [he]
  calc
    _ = (∫ q : CircleHodge.Circle,(α q)^2/ρ.val q+(β q)^2/ρ.val q)+
        ∫ q : CircleHodge.Circle,2*(α q*β q/ρ.val q) := by
      simpa only [Pi.add_apply] using integral_add
        ((energy_integrable ρ α).add (energy_integrable ρ β)) ((pairing_integrable ρ α β).const_mul 2)
    _ = _ := by rw [integral_add (energy_integrable ρ α) (energy_integrable ρ β),integral_const_mul]
theorem energy_splitting (ρ : Density) (α : Coefficient) :
    weightedEnergy ρ α=weightedEnergy ρ (representative ρ α)+
      weightedEnergy ρ (α-representative ρ α) := by
  have h:=energy_add ρ (representative ρ α) (α-representative ρ α)
  rw [add_sub_cancel,representative_orthogonal,mul_zero,add_zero] at h
  exact h
theorem representative_energy (ρ : Density) (α : Coefficient) :
    weightedEnergy ρ (representative ρ α)=(mean α)^2/mean ρ.val := by
  have he : (fun q => (representative ρ α q)^2/ρ.val q)=
      fun q => (mean α/mean ρ.val)^2*ρ.val q := by
    funext q
    change (((mean α/mean ρ.val)*ρ.val q)^2/ρ.val q)=_
    field_simp [density_ne ρ q]
  unfold weightedEnergy
  rw [he,integral_const_mul,← mean_circle]
  field_simp
theorem energy_minimum (ρ : Density) (α : Coefficient) :
    (mean α)^2/mean ρ.val≤weightedEnergy ρ α := by
  rw [energy_splitting,representative_energy]
  exact le_add_of_nonneg_right (energy_nonneg _ _)
theorem minimum_iff_representative (ρ : Density) (α : Coefficient) :
    weightedEnergy ρ α=(mean α)^2/mean ρ.val ↔ α=representative ρ α := by
  constructor
  · intro h
    have hs:=energy_splitting ρ α
    have he:=representative_energy ρ α
    have hz : weightedEnergy ρ (α-representative ρ α)=0 := by linarith
    exact sub_eq_zero.mp ((energy_zero_iff _ _).mp hz)
  · intro h
    exact (congrArg (weightedEnergy ρ) h).trans (representative_energy ρ α)


theorem representative_eq_of_exact (ρ : Density) {α β : Coefficient}
    (h : ExactCoefficient (α-β)) : representative ρ α=representative ρ β := by
  have he:=exact_mean_zero h
  rw [mean_sub] at he
  unfold representative
  rw [sub_eq_zero.mp he]
theorem class_minimum (ρ : Density) (α β : Coefficient)
    (h : ExactCoefficient (α-β)) : weightedEnergy ρ (representative ρ α)≤weightedEnergy ρ β := by
  rw [representative_eq_of_exact ρ h,representative_energy]
  exact energy_minimum ρ β
theorem class_minimum_rigid (ρ : Density) (α β : Coefficient)
    (h : ExactCoefficient (α-β)) :
    weightedEnergy ρ β=weightedEnergy ρ (representative ρ α) ↔ β=representative ρ α := by
  rw [representative_eq_of_exact ρ h,representative_energy]
  exact minimum_iff_representative ρ β
theorem representative_lineIntegral (ρ : Density) (α : Coefficient) (L : ACLift) :
    lineIntegral (representative ρ α) L=lineIntegral α L := by
  rw [lineIntegral_eq_mean,lineIntegral_eq_mean,representative_mean]
theorem representative_computational_period (ρ : Density) (α : Coefficient) (p : Trace 0 0) :
    lineIntegral (representative ρ α) (fromTrace p)=period p (meanHarmonic α) := by
  rw [representative_lineIntegral]
  exact lineIntegral_fromTrace_harmonic α p
theorem representative_homotopic_period (ρ : Density) (α : Coefficient) (L : ACLift)
    (p : Trace 0 0) (h : _root_.Path.Homotopic (projectedLoop L) (GeometricTrace.realize p)) :
    lineIntegral (representative ρ α) L=period p (meanHarmonic α) := by
  rw [representative_lineIntegral]
  exact lineIntegral_computational_harmonic α L p h
theorem finite_harmonic_unchanged (ρ : Density) (α : Coefficient) :
    meanHarmonic (representative ρ α)=meanHarmonic α := by
  apply Subtype.ext
  ext e
  change mean (representative ρ α)=mean α
  exact representative_mean ρ α
theorem all_periods_determine_representative (ρ : Density) (α β : Coefficient) :
    (∀ p : Trace 0 0,lineIntegral α (fromTrace p)=lineIntegral β (fromTrace p)) ↔
      representative ρ α=representative ρ β := by
  constructor
  · intro h
    have he:=h unitTrace
    rw [lineIntegral_unit,lineIntegral_unit] at he
    unfold representative
    rw [he]
  · intro h p
    have he:=congrArg mean h
    rw [representative_mean,representative_mean] at he
    rw [lineIntegral_eq_mean,lineIntegral_eq_mean,he]
theorem representative_exact_iff_periods (ρ : Density) (α β : Coefficient) :
    ExactCoefficient (α-β) ↔
      ∀ p : Trace 0 0,lineIntegral α (fromTrace p)=lineIntegral β (fromTrace p) := by
  constructor
  · intro h
    exact (all_periods_determine_representative ρ α β).mpr (representative_eq_of_exact ρ h)
  · intro h
    apply (mean_zero_iff_exact _).mp
    rw [mean_sub]
    have he:=h unitTrace
    rw [lineIntegral_unit,lineIntegral_unit] at he
    exact sub_eq_zero.mpr he

/-- Positive nonconstant continuous density, not a flat rescaling. -/
noncomputable def exampleDensity : Density :=
  ⟨⟨fun q => 2+(AddCircle.toCircle q : ℂ).re,by fun_prop⟩,by
    intro q
    have h : |(AddCircle.toCircle q : ℂ).re|≤1 := by
      simpa using Complex.abs_re_le_norm (AddCircle.toCircle q : ℂ)
    change 0<2+(AddCircle.toCircle q : ℂ).re
    linarith [(abs_le.mp h).1]⟩
theorem example_zero : exampleDensity.val 0=3 := by norm_num [exampleDensity]
theorem example_half : exampleDensity.val ((1/2 : ℝ) : CircleHodge.Circle)=1 := by
  change 2+(AddCircle.toCircle ((1/2 : ℝ) : CircleHodge.Circle) : ℂ).re=1
  rw [AddCircle.toCircle_apply_mk,Circle.coe_exp]
  have he : 2*Real.pi*(1/2 : ℝ)=Real.pi := by ring
  norm_num [Complex.exp_re,he]
theorem example_nonconstant : ¬∃ c : ℝ,exampleDensity.val=constant c := by
  rintro ⟨c,h⟩
  have h0:=congrArg (fun α : Coefficient => α 0) h
  have h1:=congrArg (fun α : Coefficient => α ((1/2 : ℝ) : CircleHodge.Circle)) h
  rw [example_zero] at h0
  rw [example_half] at h1
  change 3=c at h0
  change 1=c at h1
  linarith
theorem example_harmonic_nonconstant : MetricHarmonic exampleDensity exampleDensity.val ∧
    ¬HarmonicCoefficient exampleDensity.val := by
  constructor
  · exact (harmonic_iff_multiple _ _).mpr ⟨1,by simp⟩
  · exact fun h => example_nonconstant ((harmonic_iff_constant _).mp h)
theorem example_unit_representative_nonconstant :
    ¬HarmonicCoefficient (representative exampleDensity (constant 1)) := by
  intro hh
  obtain ⟨c,hc⟩:=(harmonic_iff_constant _).mp hh
  have hk : mean (constant 1)/mean exampleDensity.val≠0 := by
    rw [mean_constant]
    exact div_ne_zero one_ne_zero (ne_of_gt (mean_pos exampleDensity))
  apply example_nonconstant
  refine ⟨c/(mean (constant 1)/mean exampleDensity.val),?_⟩
  ext q
  have hq:=congrArg (fun α : Coefficient => α q) hc
  change (mean (constant 1)/mean exampleDensity.val)*exampleDensity.val q=c at hq
  change exampleDensity.val q=c/(mean (constant 1)/mean exampleDensity.val)
  exact (eq_div_iff hk).mpr (by simpa [mul_comm] using hq)


/-- Actual integration by parts for the coordinate codifferential. C1 hypotheses are explicit. -/
theorem codifferential_adjoint (ρ : Density) (α φ : Coefficient)
    (hα : ContDiff ℝ 1 (cover (starOne ρ α))) (hφ : ContDiff ℝ 1 (cover φ)) :
    (∫ x in (0 : ℝ)..1,deriv (cover φ) x*cover α x/cover ρ.val x)=
      ∫ x in (0 : ℝ)..1,cover φ x*codifferential ρ α x*cover ρ.val x := by
  have ha := hα.contDiffOn.absolutelyContinuousOnInterval (a:=0) (b:=1)
  have hp := hφ.contDiffOn.absolutelyContinuousOnInterval (a:=0) (b:=1)
  have hi := ha.integral_mul_deriv_eq_deriv_mul hp
  have h0 := cover_periodic (starOne ρ α) 0
  have h1 := cover_periodic φ 0
  simp only [zero_add] at h0 h1
  rw [h0,h1,sub_self,zero_sub] at hi
  have hl : (fun x => deriv (cover φ) x*cover α x/cover ρ.val x)=
      fun x => cover (starOne ρ α) x*deriv (cover φ) x := by
    funext x
    change _=(cover α x/cover ρ.val x)*_
    ring
  have hr : (fun x => cover φ x*codifferential ρ α x*cover ρ.val x)=
      fun x => -(deriv (cover (starOne ρ α)) x*cover φ x) := by
    funext x
    unfold codifferential
    field_simp [show cover ρ.val x≠0 from density_ne ρ (x : CircleHodge.Circle)]
  rw [hl,hi,hr,intervalIntegral.integral_neg]


end ComputationalHodge.MetricHodge
