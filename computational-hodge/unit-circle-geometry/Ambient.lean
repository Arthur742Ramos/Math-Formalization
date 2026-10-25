module
public import Energy
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Integral.CircleIntegral
@[expose] public section
namespace ComputationalHodge.UnitCircleGeometry
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts ComputationalHodge.Dirichlet
open MeasureTheory Set Complex
open scoped NNReal Topology unitInterval ComplexConjugate
noncomputable def embed (x : CircleHodge.Circle) : ℂ := (AddCircle.toCircle x : ℂ)
theorem embed_zero : embed 0=1 := by simp [embed]
theorem embed_norm (x : CircleHodge.Circle) : ‖embed x‖=1 := (AddCircle.toCircle x).norm_coe
theorem embed_injective : Function.Injective embed := by
  intro x y h
  exact AddCircle.injective_toCircle (by norm_num : (1 : ℝ)≠0) (Subtype.ext h)
noncomputable def embedMap : C(CircleHodge.Circle,ℂ) :=
  ⟨embed,continuous_subtype_val.comp AddCircle.continuous_toCircle⟩
noncomputable def embeddedPath (L : ACLift) : _root_.Path (embed 0) (embed 0) :=
  (projectedLoop L).map embedMap.continuous
theorem embedded_base (L : ACLift) : embeddedPath L 0=1 ∧ embeddedPath L 1=1 := by
  simp only [Path.source,Path.target,embed_zero,and_self]
noncomputable def curve (L : ACLift) (t : ℝ) : ℂ :=
  embeddedPath L (Set.projIcc 0 1 zero_le_one t)
theorem curve_norm (L : ACLift) (t : ℝ) : ‖curve L t‖=1 := embed_norm _
theorem embedded_fromTrace (p : Trace 0 0) :
    embeddedPath (fromTrace p)=(GeometricTrace.realize p).map embedMap.continuous := by
  ext t
  change embed (projectedLoop (fromTrace p) t)=embed (GeometricTrace.realize p t)
  rw [projected_fromTrace]
theorem curve_eq_on (L : ACLift) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    curve L t=embed ((L.val t : ℝ) : CircleHodge.Circle) := by
  change embed ((L.val (Set.projIcc 0 1 zero_le_one t) : ℝ) : CircleHodge.Circle)=_
  rw [Set.projIcc_of_mem zero_le_one ht]
theorem embed_coe (x : ℝ) : embed (x : CircleHodge.Circle)=circleMap 0 1 (2*Real.pi*x) := by
  simp [embed,AddCircle.toCircle_apply_mk,Circle.coe_exp,circleMap]
theorem curve_deriv (L : ACLift) {t : ℝ} (ht : t∈Ioo (0 : ℝ) 1)
    (hd : DifferentiableAt ℝ L.val t) :
    deriv (curve L) t=curve L t*Complex.I*((2*Real.pi*deriv L.val t : ℝ) : ℂ) := by
  have he : curve L=ᶠ[nhds t] (fun x => circleMap 0 1 (2*Real.pi*L.val x)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    rw [curve_eq_on L ⟨hx.1.le,hx.2.le⟩,embed_coe]
  rw [he.deriv_eq]
  have h := (hasDerivAt_circleMap 0 1 (2*Real.pi*L.val t)).scomp t
    (hd.hasDerivAt.const_mul (2*Real.pi))
  rw [curve_eq_on L ⟨ht.1.le,ht.2.le⟩,embed_coe]
  simpa only [Function.comp_def,Complex.real_smul,mul_comm] using h.deriv
theorem derivative_ae (L : ACLift) :
    ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
      deriv (curve L) t=curve L t*Complex.I*((2*Real.pi*deriv L.val t : ℝ) : ℂ) := by
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc : Ioo (0 : ℝ) 1=ᵐ[volume] Ioc 0 1)]
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae L.property.1.ae_differentiableAt] with t ht hd
  exact curve_deriv L ht (hd (by simpa [uIcc_of_le zero_le_one] using ⟨ht.1.le,ht.2.le⟩))
/-- Actual real-linear angular covector. It is normalized on the unit-circle image. -/
noncomputable def angularForm (z : ℂ) : ℂ →ₗ[ℝ] ℝ where
  toFun v := (conj z*v).im/(2*Real.pi)
  map_add' u v := by simp [mul_add,add_div]
  map_smul' r v := by simp [smul_eq_mul];ring
theorem angular_tangent (z : ℂ) (hz : ‖z‖=1) (a : ℝ) :
    angularForm z (z*Complex.I*((2*Real.pi*a : ℝ) : ℂ))=a := by
  have hn : conj z*z=1 := by
    simpa only [hz,one_pow,Complex.ofReal_one] using Complex.conj_mul' z
  change (conj z*(z*Complex.I*((2*Real.pi*a : ℝ) : ℂ))).im/(2*Real.pi)=a
  have he : conj z*(z*Complex.I*((2*Real.pi*a : ℝ) : ℂ))=
      (conj z*z)*Complex.I*((2*Real.pi*a : ℝ) : ℂ) := by ring
  rw [he,hn,one_mul]
  simp [Complex.mul_im,Real.pi_ne_zero]
theorem angular_pullback_ae (L : ACLift) :
    (fun t => angularForm (curve L t) (deriv (curve L) t))
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] deriv L.val := by
  filter_upwards [derivative_ae L] with t ht
  rw [ht];exact angular_tangent _ (curve_norm L t) _
theorem angular_integrable (L : ACLift) :
    IntervalIntegrable (fun t => angularForm (curve L t) (deriv (curve L) t)) volume 0 1 := by
  apply L.property.1.intervalIntegrable_deriv.congr_ae
  simpa only [uIoc_of_le zero_le_one] using (angular_pullback_ae L).symm
noncomputable def angularIntegral (L : ACLift) : ℝ :=
  ∫ t in (0 : ℝ)..1,angularForm (curve L t) (deriv (curve L) t)
theorem angular_integral (L : ACLift) : angularIntegral L=L.val 1 := by
  unfold angularIntegral
  calc
    _ = ∫ t in (0 : ℝ)..1,deriv L.val t := intervalIntegral.integral_congr_ae_restrict (by
      simpa only [uIoc_of_le zero_le_one] using angular_pullback_ae L)
    _ = _ := derivative_integral L
theorem speed_squared_ae (L : ACLift) :
    (fun t => ‖deriv (curve L) t‖^2)=ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun t => (2*Real.pi)^2*(deriv L.val t)^2) := by
  filter_upwards [derivative_ae L] with t ht
  rw [ht,norm_mul,norm_mul,curve_norm,Complex.norm_I,one_mul,one_mul,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow]
def AmbientFiniteEnergy (L : ACLift) : Prop :=
  IntervalIntegrable (fun t => ‖deriv (curve L) t‖^2) volume 0 1
noncomputable def ambientEnergy (L : ACLift) : ℝ := ∫ t in (0 : ℝ)..1,‖deriv (curve L) t‖^2
theorem finite_energy_iff (L : ACLift) : AmbientFiniteEnergy L ↔ FiniteEnergy L := by
  constructor
  · intro h
    have hs : IntervalIntegrable (fun t => (2*Real.pi)^2*(deriv L.val t)^2) volume 0 1 :=
      h.congr_ae (by simpa only [uIoc_of_le zero_le_one] using speed_squared_ae L)
    apply (hs.const_mul ((2*Real.pi)^2)⁻¹).congr
    intro t ht
    field_simp
  · intro h
    exact (h.const_mul ((2*Real.pi)^2)).congr_ae (by
      simpa only [uIoc_of_le zero_le_one] using (speed_squared_ae L).symm)
theorem ambient_energy (L : ACLift) : ambientEnergy L=(2*Real.pi)^2*energy L := by
  unfold ambientEnergy energy
  calc
    _ = ∫ t in (0 : ℝ)..1,(2*Real.pi)^2*(deriv L.val t)^2 :=
      intervalIntegral.integral_congr_ae_restrict (by
        simpa only [uIoc_of_le zero_le_one] using speed_squared_ae L)
    _ = _ := intervalIntegral.integral_const_mul _ _
theorem angular_computational (p : Trace 0 0) : angularIntegral (fromTrace p)=period p unitCochain := by
  rw [angular_integral,period_unit_count]
  change actualLift p 1=(count p : ℝ)
  rw [actualLift_eq_rawLift,rawLift_one]
theorem angular_harmonic (α : Coefficient) (p : Trace 0 0) :
    mean α*angularIntegral (fromTrace p)=period p (meanHarmonic α) := by
  rw [angular_computational,period_unit_count]
  exact (period_mean_count α p).symm
noncomputable def circlePath (L : ACLift) :
    _root_.Path (AddCircle.toCircle (0 : CircleHodge.Circle)) (AddCircle.toCircle (0 : CircleHodge.Circle)) :=
  (projectedLoop L).map AddCircle.continuous_toCircle
theorem circle_path_base (L : ACLift) : circlePath L 0=1 ∧ circlePath L 1=1 := by
  simp only [Path.source,Path.target,AddCircle.toCircle_zero,and_self]
theorem curve_from_circlePath (L : ACLift) (t : ℝ) :
    curve L t=(circlePath L (Set.projIcc 0 1 zero_le_one t) : ℂ) := rfl
theorem circle_homotopy (L : ACLift) :
    _root_.Path.Homotopic (circlePath L) (circlePath (affine L)) :=
  (affine_homotopic L).map ⟨AddCircle.toCircle,AddCircle.continuous_toCircle⟩
theorem curve_eq_iff (L M : ACLift) : curve L=curve M ↔ EqOn L.val M.val (Icc 0 1) := by
  constructor
  · intro h
    have hp : projectedLoop L=projectedLoop M := by
      ext t
      apply embed_injective
      have hh := congrFun h (t : ℝ)
      rwa [curve_eq_on L t.property,curve_eq_on M t.property] at hh
    intro t ht
    rw [← actual_lift_on_interval L ⟨t,ht⟩,← actual_lift_on_interval M ⟨t,ht⟩,hp]
  · intro h
    funext t
    have ht := (Set.projIcc 0 1 zero_le_one t).property
    change embed ((L.val (Set.projIcc 0 1 zero_le_one t) : ℝ) : CircleHodge.Circle)=
      embed ((M.val (Set.projIcc 0 1 zero_le_one t) : ℝ) : CircleHodge.Circle)
    rw [h ht]
theorem ambient_minimum_rigid (L : ACLift) (h : AmbientFiniteEnergy L) :
    ambientEnergy L=(2*Real.pi)^2*(L.val 1)^2 ↔ curve L=curve (affine L) := by
  rw [ambient_energy,mul_right_inj' (by positivity : (2*Real.pi)^2≠0),
    curve_eq_iff,minimum_iff_affine L ((finite_energy_iff L).mp h)]
theorem ambient_class_minimum (L M : ACLift) (h : AmbientFiniteEnergy M)
    (hm : _root_.Path.Homotopic (projectedLoop L) (projectedLoop M)) :
    ambientEnergy (affine L)≤ambientEnergy M := by
  rw [ambient_energy,ambient_energy]
  exact mul_le_mul_of_nonneg_left (class_minimum L M ((finite_energy_iff M).mp h) hm) (sq_nonneg _)
theorem raw_finite_energy (p : Trace 0 0) : AmbientFiniteEnergy (fromTrace p) :=
  (finite_energy_iff _).mpr (fromTrace_finite p)
theorem computational_energy_minimum (p : Trace 0 0) :
    ambientEnergy (affine (fromTrace p))=(2*Real.pi)^2*(period p unitCochain)^2 := by
  rw [ambient_energy,computational_minimum]
theorem paused_strict : (2*Real.pi)^2<ambientEnergy (fromTrace paused) := by
  rw [ambient_energy]
  exact lt_mul_of_one_lt_right (by positivity : (0 : ℝ)<(2*Real.pi)^2) paused_energy_strict
end ComputationalHodge.UnitCircleGeometry
