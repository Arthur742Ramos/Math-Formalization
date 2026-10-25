module
public import Primitive
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.MonotoneContinuity
@[expose] public section
namespace ComputationalHodge.Arclength
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.LoopCharacters
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts
open ComputationalHodge.Dirichlet ComputationalHodge.MetricHodge
open MeasureTheory Set
open scoped Topology NNReal unitInterval

theorem density_bounds (ρ : Density) : ∃ c C : ℝ,0<c ∧ 0<C ∧
    ∀ q,c≤ρ.val q ∧ ρ.val q≤C := by
  obtain ⟨c,hc,hlo⟩ := isCompact_univ.exists_forall_le'
    ρ.val.continuous.continuousOn (fun q _ => ρ.property q)
  obtain ⟨C,hC⟩ := (isCompact_range ρ.val.continuous).isBounded.exists_norm_le
  have hupper (q : CircleHodge.Circle) : ρ.val q≤C :=
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC _ ⟨q,rfl⟩)
  exact ⟨c,C,hc,(ρ.property 0).trans_le (hupper 0),fun q => ⟨hlo q (mem_univ _),hupper q⟩⟩
noncomputable def coordinate (ρ : Density) (x : ℝ) : ℝ := primitive ρ.val x/mean ρ.val
theorem coordinate_hasDerivAt (ρ : Density) (x : ℝ) :
    HasDerivAt (coordinate ρ) (cover ρ.val x/mean ρ.val) x :=
  (primitive_hasDerivAt ρ.val x).div_const _
theorem coordinate_zero (ρ : Density) : coordinate ρ 0=0 := by simp [coordinate,primitive]
theorem coordinate_lipschitz (ρ : Density) : ∃ K : ℝ≥0,LipschitzWith K (coordinate ρ) := by
  obtain ⟨_,C,_,hC,hbound⟩:=density_bounds ρ
  refine ⟨⟨C/mean ρ.val,(div_pos hC (mean_pos ρ)).le⟩,
    lipschitzWith_of_nnnorm_deriv_le (fun x => (coordinate_hasDerivAt ρ x).differentiableAt) (fun x => ?_)⟩
  rw [(coordinate_hasDerivAt ρ x).deriv]
  change ‖ρ.val (x : CircleHodge.Circle)/mean ρ.val‖≤C/mean ρ.val
  rw [Real.norm_eq_abs,abs_of_pos (div_pos (ρ.property (x : CircleHodge.Circle)) (mean_pos ρ))]
  exact div_le_div_of_nonneg_right (hbound (x : CircleHodge.Circle)).2 (mean_pos ρ).le
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
theorem inverse_zero (ρ : Density) : inverse ρ 0=0 := by
  apply (coordinate_strictMono ρ).injective
  rw [coordinate_inverse,coordinate_zero]
theorem inverse_int (ρ : Density) (n : ℤ) : inverse ρ (n : ℝ)=n := by
  apply (coordinate_strictMono ρ).injective
  rw [coordinate_inverse,coordinate_int]
theorem inverse_hasDerivAt (ρ : Density) (x : ℝ) :
    HasDerivAt (inverse ρ) (mean ρ.val/cover ρ.val (inverse ρ x)) x := by
  have h := HasDerivAt.of_local_left_inverse
    (coordinateHomeomorph ρ).symm.continuous.continuousAt
    (coordinate_hasDerivAt ρ (inverse ρ x))
    (ne_of_gt (div_pos (ρ.property _) (mean_pos ρ)))
    (Filter.Eventually.of_forall (coordinate_inverse ρ))
  simpa only [inverse,inv_div] using h
theorem inverse_lipschitz (ρ : Density) : ∃ K : ℝ≥0,LipschitzWith K (inverse ρ) := by
  obtain ⟨c,C,hc,_,hbound⟩:=density_bounds ρ
  refine ⟨⟨mean ρ.val/c,(div_pos (mean_pos ρ) hc).le⟩,
    lipschitzWith_of_nnnorm_deriv_le (fun x => (inverse_hasDerivAt ρ x).differentiableAt) (fun x => ?_)⟩
  rw [(inverse_hasDerivAt ρ x).deriv]
  change ‖mean ρ.val/ρ.val ((inverse ρ x : ℝ) : CircleHodge.Circle)‖≤mean ρ.val/c
  rw [Real.norm_eq_abs,abs_of_pos (div_pos (mean_pos ρ) (ρ.property ((inverse ρ x : ℝ) : CircleHodge.Circle)))]
  exact div_le_div_of_nonneg_left (mean_pos ρ).le hc (hbound ((inverse ρ x : ℝ) : CircleHodge.Circle)).1
theorem coordinate_endpoint (ρ : Density) (L : ACLift) : coordinate ρ (L.val 1)=L.val 1 := by
  obtain ⟨n,hn⟩:=(AddCircle.coe_eq_zero_iff (p:=(1 : ℝ))).mp L.property.2.2
  have he : (n : ℝ)=L.val 1 := by simpa using hn
  rw [← he,coordinate_int]
noncomputable def transformed (ρ : Density) (L : ACLift) : ACLift :=
  ⟨fun t => coordinate ρ (L.val t),by
    obtain ⟨K,hK⟩:=coordinate_lipschitz ρ
    exact hK.comp_absolutelyContinuousOnInterval L.property.1,
    by change coordinate ρ (L.val 0)=0;rw [L.property.2.1,coordinate_zero],
    by change ((coordinate ρ (L.val 1) : ℝ) : CircleHodge.Circle)=0;rw [coordinate_endpoint];exact L.property.2.2⟩
theorem transformed_endpoint (ρ : Density) (L : ACLift) : (transformed ρ L).val 1=L.val 1 :=
  coordinate_endpoint ρ L
noncomputable def minimizer (ρ : Density) (L : ACLift) : ACLift :=
  ⟨fun t => inverse ρ (L.val 1*t),by
    obtain ⟨K,hK⟩:=inverse_lipschitz ρ
    exact hK.comp_absolutelyContinuousOnInterval
      ((LipschitzWith.id : LipschitzWith 1 (id : ℝ→ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval.const_mul (L.val 1)),
    by simp [inverse_zero],by
      obtain ⟨n,hn⟩:=(AddCircle.coe_eq_zero_iff (p:=(1 : ℝ))).mp L.property.2.2
      have he : (n : ℝ)=L.val 1 := by simpa using hn
      simp only [mul_one]
      rw [← he,inverse_int]
      simp⟩
theorem minimizer_endpoint (ρ : Density) (L : ACLift) : (minimizer ρ L).val 1=L.val 1 := by
  obtain ⟨n,hn⟩:=(AddCircle.coe_eq_zero_iff (p:=(1 : ℝ))).mp L.property.2.2
  have he : (n : ℝ)=L.val 1 := by simpa using hn
  change inverse ρ (L.val 1*1)=L.val 1
  rw [mul_one,← he,inverse_int]
theorem transformed_minimizer (ρ : Density) (L : ACLift) : transformed ρ (minimizer ρ L)=affine L := by
  apply Subtype.ext
  funext t
  exact coordinate_inverse ρ (L.val 1*t)

/-- The actual squared speed for the circle length convention ds=ρ dx; no factor 1/2. -/
noncomputable def energy (ρ : Density) (L : ACLift) : ℝ :=
  ∫ t in (0 : ℝ)..1,(cover ρ.val (L.val t)*deriv L.val t)^2
def WeightedFiniteEnergy (ρ : Density) (L : ACLift) : Prop :=
  IntervalIntegrable (fun t => (cover ρ.val (L.val t)*deriv L.val t)^2) volume 0 1

theorem square_ae (ρ : Density) (L : ACLift) :
    ∀ᵐ t : ℝ,t∈uIoc (0 : ℝ) 1 →
      (cover ρ.val (L.val t)*deriv L.val t)^2=
        (mean ρ.val)^2*(deriv (transformed ρ L).val t)^2 := by
  filter_upwards [L.property.1.ae_differentiableAt] with t ht hm
  have hm' : t∈uIcc (0 : ℝ) 1 := by
    simp only [uIoc_of_le zero_le_one] at hm
    simpa only [uIcc_of_le zero_le_one] using (show t∈Icc (0 : ℝ) 1 from ⟨hm.1.le,hm.2⟩)
  have hd := ((coordinate_hasDerivAt ρ (L.val t)).comp t (ht hm').hasDerivAt).deriv
  change deriv (transformed ρ L).val t=(cover ρ.val (L.val t)/mean ρ.val)*deriv L.val t at hd
  rw [hd]
  field_simp [ne_of_gt (mean_pos ρ)]

theorem energy_identity (ρ : Density) (L : ACLift) :
    energy ρ L=(mean ρ.val)^2*Dirichlet.energy (transformed ρ L) := by
  unfold energy Dirichlet.energy
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr_ae (square_ae ρ L)

theorem finite_iff (ρ : Density) (L : ACLift) :
    WeightedFiniteEnergy ρ L ↔ Dirichlet.FiniteEnergy (transformed ρ L) := by
  have he : (fun t => (cover ρ.val (L.val t)*deriv L.val t)^2)=ᵐ[volume.restrict (uIoc (0 : ℝ) 1)]
      (fun t => (mean ρ.val)^2*(deriv (transformed ρ L).val t)^2) :=
    (ae_restrict_iff' measurableSet_uIoc).mpr (square_ae ρ L)
  constructor
  · intro h
    have hh : Dirichlet.FiniteEnergy (transformed ρ L) :=
      (h.const_mul ((mean ρ.val)^2)⁻¹).congr_ae ?_
    · exact hh
    filter_upwards [he] with t ht
    rw [ht]
    field_simp [ne_of_gt (mean_pos ρ)]
  · intro h
    exact (h.const_mul ((mean ρ.val)^2)).congr_ae he.symm

theorem minimizer_finite (ρ : Density) (L : ACLift) : WeightedFiniteEnergy ρ (minimizer ρ L) := by
  rw [finite_iff,transformed_minimizer]
  exact affine_finite L
theorem minimizer_energy (ρ : Density) (L : ACLift) :
    energy ρ (minimizer ρ L)=(mean ρ.val*L.val 1)^2 := by
  rw [energy_identity,transformed_minimizer,affine_energy]
  ring
theorem energy_lower_bound (ρ : Density) (L : ACLift) (h : WeightedFiniteEnergy ρ L) :
    (mean ρ.val*L.val 1)^2≤energy ρ L := by
  rw [energy_identity,mul_pow]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [transformed_endpoint] using Dirichlet.energy_lower_bound (transformed ρ L) ((finite_iff ρ L).mp h))
    (sq_nonneg _)

theorem minimum_iff (ρ : Density) (L : ACLift) (h : WeightedFiniteEnergy ρ L) :
    energy ρ L=(mean ρ.val*L.val 1)^2 ↔ EqOn L.val (minimizer ρ L).val (Icc 0 1) := by
  rw [energy_identity,mul_pow,mul_eq_mul_left_iff]
  have hn : (mean ρ.val)^2≠0 := pow_ne_zero 2 (ne_of_gt (mean_pos ρ))
  simp only [hn,or_false]
  rw [← transformed_endpoint ρ L,minimum_iff_affine _ ((finite_iff ρ L).mp h)]
  constructor
  · intro he t ht
    apply (coordinate_strictMono ρ).injective
    have hh := he ht
    change coordinate ρ (L.val t)=(transformed ρ L).val 1*t at hh
    rw [transformed_endpoint] at hh
    exact hh.trans (coordinate_inverse ρ (L.val 1*t)).symm
  · intro he t ht
    change coordinate ρ (L.val t)=(transformed ρ L).val 1*t
    rw [transformed_endpoint,he ht]
    exact coordinate_inverse ρ (L.val 1*t)

theorem minimizer_homotopic (ρ : Density) (L : ACLift) :
    _root_.Path.Homotopic (projectedLoop L) (projectedLoop (minimizer ρ L)) := by
  have he : affine L=affine (minimizer ρ L) := by
    apply Subtype.ext
    funext t
    change L.val 1*t=(minimizer ρ L).val 1*t
    rw [minimizer_endpoint]
  exact (affine_homotopic L).trans (by rw [he];exact (affine_homotopic (minimizer ρ L)).symm)

theorem finite_of_lipschitz (ρ : Density) (L : ACLift) {K : ℝ≥0}
    (hL : LipschitzWith K L.val) : WeightedFiniteEnergy ρ L := by
  rw [finite_iff]
  obtain ⟨C,hC⟩:=coordinate_lipschitz ρ
  have hK : LipschitzWith (C*K) (transformed ρ L).val := hC.comp hL
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr
  apply IntegrableOn.of_bound (measure_Icc_lt_top)
    ((aestronglyMeasurable_deriv (transformed ρ L).val _).pow 2) (((C*K : ℝ≥0) : ℝ)^2)
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hn := norm_deriv_le_of_lipschitz (x₀:=t) hK
  change (deriv (transformed ρ L).val t)^2≤((C*K : ℝ≥0) : ℝ)^2
  simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hn 2

theorem fromTrace_finite (ρ : Density) (p : Trace 0 0) : WeightedFiniteEnergy ρ (fromTrace p) := by
  obtain ⟨K,hK⟩:=rawLift_lipschitz p
  rw [← actualLift_eq_rawLift] at hK
  exact finite_of_lipschitz ρ (fromTrace p) hK

theorem class_minimum (ρ : Density) (L M : ACLift) (h : WeightedFiniteEnergy ρ M)
    (hm : _root_.Path.Homotopic (projectedLoop L) (projectedLoop M)) :
    energy ρ (minimizer ρ L)≤energy ρ M := by
  have he : L.val 1=M.val 1 := by
    rw [← projected_winding,← projected_winding];exact winding_homotopic hm
  rw [minimizer_energy,he]
  exact energy_lower_bound ρ M h

theorem computational_minimum (ρ : Density) (p : Trace 0 0) :
    energy ρ (minimizer ρ (fromTrace p))=(period p (meanHarmonic ρ.val).val)^2 := by
  rw [minimizer_energy]
  change (mean ρ.val*actualLift p 1)^2=(period p (meanCochain ρ.val))^2
  rw [actualLift_eq_rawLift,rawLift_one,period_mean_count]

theorem class_minimum_iff (ρ : Density) (L M : ACLift) (h : WeightedFiniteEnergy ρ M)
    (hm : _root_.Path.Homotopic (projectedLoop L) (projectedLoop M)) :
    energy ρ M=energy ρ (minimizer ρ L) ↔ EqOn M.val (minimizer ρ L).val (Icc 0 1) := by
  have he : M.val 1=L.val 1 := by
    rw [← projected_winding,← projected_winding];exact (winding_homotopic hm).symm
  have hh : minimizer ρ M=minimizer ρ L := by
    apply Subtype.ext
    funext t
    change inverse ρ (M.val 1*t)=inverse ρ (L.val 1*t)
    rw [he]
  rw [← hh,minimizer_energy]
  exact minimum_iff ρ M h

noncomputable def unitLift : ACLift :=
  ⟨id,(LipschitzWith.id : LipschitzWith 1 (id : ℝ→ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval,
    rfl,by simp⟩
theorem unitLift_finite (ρ : Density) : WeightedFiniteEnergy ρ unitLift :=
  finite_of_lipschitz ρ unitLift LipschitzWith.id

theorem unit_minimum_forces_density (ρ : Density) (he : energy ρ unitLift=(mean ρ.val)^2)
    (x : ℝ) (hx : x∈Ioo (0 : ℝ) 1) : cover ρ.val x=mean ρ.val := by
  have he' : energy ρ unitLift=(mean ρ.val*unitLift.val 1)^2 := by simpa [unitLift] using he
  have hh := (minimum_iff ρ unitLift (unitLift_finite ρ)).mp he'
  have hc (y : ℝ) (hy : y∈Icc (0 : ℝ) 1) : coordinate ρ y=y := by
    have h := congrArg (coordinate ρ) (hh hy)
    change coordinate ρ y=coordinate ρ (inverse ρ (1*y)) at h
    simpa only [one_mul,coordinate_inverse] using h
  have hf : coordinate ρ=ᶠ[nhds x] id := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hc y ⟨hy.1.le,hy.2.le⟩
  have hd : cover ρ.val x/mean ρ.val=1 := by
    rw [← (coordinate_hasDerivAt ρ x).deriv,hf.deriv_eq]
    exact deriv_id x
  exact (div_eq_iff (ne_of_gt (mean_pos ρ))).mp hd |>.trans (one_mul _)

theorem example_quarter : exampleDensity.val ((1/4 : ℝ) : CircleHodge.Circle)=2 := by
  change 2+(AddCircle.toCircle ((1/4 : ℝ) : CircleHodge.Circle) : ℂ).re=2
  rw [AddCircle.toCircle_apply_mk,Circle.coe_exp]
  have he : 2*Real.pi*(1/4 : ℝ)=Real.pi/2 := by ring
  norm_num [Complex.exp_re,he]

/-- A nonconstant metric has a strictly better admitted path than the flat affine unit loop. -/
theorem example_strict : energy exampleDensity (minimizer exampleDensity unitLift)<
    energy exampleDensity unitLift := by
  apply lt_of_le_of_ne
  · rw [minimizer_energy]
    exact energy_lower_bound exampleDensity unitLift (unitLift_finite exampleDensity)
  · intro he
    have hh : energy exampleDensity unitLift=(mean exampleDensity.val)^2 := by
      rw [← he,minimizer_energy];simp [unitLift]
    have hq:=unit_minimum_forces_density exampleDensity hh (1/4) (by norm_num)
    have hr:=unit_minimum_forces_density exampleDensity hh (1/2) (by norm_num)
    change exampleDensity.val ((1/4 : ℝ) : CircleHodge.Circle)=_ at hq
    change exampleDensity.val ((1/2 : ℝ) : CircleHodge.Circle)=_ at hr
    rw [example_quarter] at hq
    rw [example_half] at hr
    linarith

end ComputationalHodge.Arclength
