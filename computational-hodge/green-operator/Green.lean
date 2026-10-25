module
public import Poisson
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
@[expose] public section
namespace ComputationalHodge.GreenOperator
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson
open ComputationalHodge.ACLifts ComputationalHodge.LoopCharacters ComputationalHodge.TraceIntegrals
open ComputationalPaths.Path.GeometricTopology MeasureTheory Set
open scoped Topology NNReal unitInterval ContDiff
theorem norm_of_positive {x : ℝ} (hx : 0<x) : ‖x‖=x := (Real.norm_eq_abs x).trans (abs_of_pos hx)

theorem weightedMean_add (ρ : RegularDensity) (f g : Coefficient) :
    weightedMean ρ (f+g)=weightedMean ρ f+weightedMean ρ g := by
  unfold weightedMean
  rw [mul_add]
  exact intervalIntegral.integral_add ((cover_continuous (ρ.val.val*f)).intervalIntegrable 0 1)
    ((cover_continuous (ρ.val.val*g)).intervalIntegrable 0 1)
theorem weightedMean_smul (ρ : RegularDensity) (c : ℝ) (f : Coefficient) :
    weightedMean ρ (c•f)=c*weightedMean ρ f := by
  have h : ρ.val.val*(c•f)=c•(ρ.val.val*f) := by ext q;change _*(c*_) = c*(_*_);ring
  rw [weightedMean,h,mean_smul]
  rfl
theorem weightedMean_bound (ρ : RegularDensity) (f : Coefficient) :
    ‖weightedMean ρ f‖≤mean ρ.val.val*‖f‖ := by
  rw [weightedMean,mean_circle]
  calc
    _ ≤ ∫ q : CircleHodge.Circle,‖ρ.val.val q*f q‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ q : CircleHodge.Circle,ρ.val.val q*‖f‖ := integral_mono
      (continuous_integrable ((ρ.val.val.continuous.mul f.continuous).norm))
      (continuous_integrable (ρ.val.val.continuous.mul_const ‖f‖))
      (fun q => by rw [norm_mul,norm_of_positive (ρ.val.property q)];exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm q) (ρ.val.property q).le)
    _ = mean ρ.val.val*‖f‖ := by rw [integral_mul_const,← mean_circle]

/-- Actual continuous weighted-mean functional, bounded using the positive density integral. -/
noncomputable def meanFunctional (ρ : RegularDensity) : Coefficient →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    {toFun:=weightedMean ρ,map_add':=weightedMean_add ρ,map_smul':=fun c f => weightedMean_smul ρ c f}
    (mean ρ.val.val) (weightedMean_bound ρ)
/-- Closed subspace of continuous forcing with vanishing actual computational obstruction. -/
noncomputable def compatibleSpace (ρ : RegularDensity) : Submodule ℝ Coefficient := (meanFunctional ρ).ker
abbrev Compatible (ρ : RegularDensity) := ↥(compatibleSpace ρ)
theorem compatible_iff (ρ : RegularDensity) (f : Coefficient) :
    f∈compatibleSpace ρ ↔ weightedMean ρ f=0 := Iff.rfl
theorem compatible_closed (ρ : RegularDensity) : IsClosed (compatibleSpace ρ : Set Coefficient) :=
  (meanFunctional ρ).isClosed_ker
instance compatible_complete (ρ : RegularDensity) : CompleteSpace (Compatible ρ) :=
  (compatible_closed ρ).completeSpace_coe
theorem compatible_iff_raw (ρ : RegularDensity) (f : Coefficient) :
    f∈compatibleSpace ρ ↔ ∀ p : Trace 0 0,lineIntegral (ρ.val.val*f) (fromTrace p)=0 :=
  ⟨fun h p => by rw [lineIntegral_eq_mean,show mean (ρ.val.val*f)=0 from h,zero_mul],
   fun h => by change mean (ρ.val.val*f)=0;simpa only [lineIntegral_unit] using h unitTrace⟩
theorem compatible_iff_periods (ρ : RegularDensity) (f : Coefficient) :
    f∈compatibleSpace ρ ↔ ∀ p : Trace 0 0,period p (meanHarmonic (ρ.val.val*f)).val=0 := by
  rw [compatible_iff_raw];simp only [lineIntegral_fromTrace_harmonic]

/-- A quantitative actual primitive estimate; the bound is proved, not assumed for Green. -/
theorem potential_weight_bound (ρ : RegularDensity) (f : Coefficient) (hf : mean f=0)
    (C : ℝ) (hC : 0≤C) (h : ∀ q,‖f q‖≤C*ρ.val.val q) : ‖potential f‖≤C*mean ρ.val.val := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hC (mean_pos ρ.val).le)).mpr
  intro q
  let x := AddCircle.equivIco (1 : ℝ) 0 q
  have hx : (x : ℝ)∈Icc (0 : ℝ) 1 := ⟨x.property.1,by simpa using x.property.2.le⟩
  have hq : ((x : ℝ) : CircleHodge.Circle)=q := AddCircle.coe_equivIco
  rw [← hq]
  change ‖(∫ t in (0 : ℝ)..(x : ℝ),cover f t)-(x : ℝ)*mean f‖≤_
  rw [hf,mul_zero,sub_zero]
  exact (intervalIntegral.norm_integral_le_of_norm_le hx.1
      (Filter.Eventually.of_forall (fun t _ => h (t : CircleHodge.Circle)))
      ((continuous_const.mul (cover_continuous ρ.val.val)).intervalIntegrable 0 x)).trans
    ((intervalIntegral.integral_mono_interval (le_refl 0) hx.1 hx.2
      (Filter.Eventually.of_forall (fun t => mul_nonneg hC (ρ.val.property (t : CircleHodge.Circle)).le))
      ((continuous_const.mul (cover_continuous ρ.val.val)).intervalIntegrable 0 1)).trans_eq (intervalIntegral.integral_const_mul C _))
theorem primitive_bound (ρ : RegularDensity) (f : Coefficient) (hf : weightedMean ρ f=0) :
    ‖firstPrimitive ρ f‖≤mean ρ.val.val*‖f‖ := by
  have h:=potential_weight_bound ρ (ρ.val.val*f) hf ‖f‖ (norm_nonneg f)
    (fun q => by
      rw [ContinuousMap.mul_apply,norm_mul,norm_of_positive (ρ.val.property q)]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (f.norm_coe_le_norm q) (ρ.val.property q).le)
  simpa only [firstPrimitive,mul_comm] using h
theorem fluxConstant_bound (ρ : RegularDensity) (f : Coefficient) :
    ‖fluxConstant ρ f‖≤‖firstPrimitive ρ f‖ := by
  rw [fluxConstant,norm_div,norm_of_positive (mean_pos ρ.val)]
  exact (div_le_iff₀ (mean_pos ρ.val)).mpr (by simpa [mul_comm] using weightedMean_bound ρ (firstPrimitive ρ f))
theorem velocity_point_bound (ρ : RegularDensity) (f : Coefficient) (hf : weightedMean ρ f=0)
    (q : CircleHodge.Circle) : ‖velocity ρ f q‖≤(2*mean ρ.val.val*‖f‖)*ρ.val.val q := by
  change ‖ρ.val.val q*(fluxConstant ρ f-firstPrimitive ρ f q)‖≤_
  rw [norm_mul,norm_of_positive (ρ.val.property q)]
  calc
    _ ≤ ρ.val.val q*(‖fluxConstant ρ f‖+‖firstPrimitive ρ f q‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (ρ.val.property q).le
    _ ≤ ρ.val.val q*(2*(mean ρ.val.val*‖f‖)) := mul_le_mul_of_nonneg_left
      (by linarith [primitive_bound ρ f hf,fluxConstant_bound ρ f,(firstPrimitive ρ f).norm_coe_le_norm q]) (ρ.val.property q).le
    _ = _ := by ring
theorem base_bound (ρ : RegularDensity) (f : Coefficient) (hf : weightedMean ρ f=0) :
    ‖(baseSolution ρ f).val‖≤2*(mean ρ.val.val)^2*‖f‖ := by
  have h:=potential_weight_bound ρ (velocity ρ f) (velocity_mean_zero ρ f)
    (2*mean ρ.val.val*‖f‖) (mul_nonneg (mul_nonneg (by norm_num) (mean_pos ρ.val).le) (norm_nonneg f)) (velocity_point_bound ρ f hf)
  change ‖potential (velocity ρ f)‖≤_
  exact h.trans_eq (by ring)
theorem normalize_bound (ρ : RegularDensity) (u : C2Coefficient) :
    ‖(normalize ρ u).val‖≤2*‖u.val‖ := by
  have h : ‖weightedMean ρ u.val/mean ρ.val.val‖≤‖u.val‖ := by
    rw [norm_div,norm_of_positive (mean_pos ρ.val)]
    exact (div_le_iff₀ (mean_pos ρ.val)).mpr (by simpa [mul_comm] using weightedMean_bound ρ u.val)
  change ‖u.val-constant (weightedMean ρ u.val/mean ρ.val.val)‖≤_
  have hc : ‖constant (weightedMean ρ u.val/mean ρ.val.val)‖≤‖u.val‖ := (ContinuousMap.norm_le_of_nonempty _).mpr (fun _ => h)
  exact (norm_sub_le _ _).trans (by linarith)
theorem green_bound (ρ : RegularDensity) (f : Coefficient) (hf : weightedMean ρ f=0) :
    ‖(green ρ f).val‖≤4*(mean ρ.val.val)^2*‖f‖ := by
  rw [green,project_eq_self ρ f hf]
  exact (normalize_bound ρ _).trans (by nlinarith [base_bound ρ f hf])

theorem gradient_smul (c : ℝ) (u : C2Coefficient) : gradient (c•u)=c•gradient u :=
  ContinuousMap.ext fun q => Quotient.inductionOn q fun x => (((contDiff_one_iff_deriv.mp (c2_c1 u)).1 x).hasDerivAt.const_mul c).deriv
theorem flux_smul (ρ : RegularDensity) (c : ℝ) (u : C2Coefficient) : flux ρ (c•u)=c•flux ρ u :=
  ContinuousMap.ext fun q => (congrArg (fun f : Coefficient => f q/ρ.val.val q) (gradient_smul c u)).trans (mul_div_assoc c (gradient u q) (ρ.val.val q))
theorem laplacian_smul (ρ : RegularDensity) (c : ℝ) (u : C2Coefficient) :
    laplacian ρ (c•u)=c•laplacian ρ u := by
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change -(deriv (cover (flux ρ (c•u))) x)/cover ρ.val.val x=_
  rw [flux_smul]
  change -(deriv (fun t => c*cover (flux ρ u) t) x)/cover ρ.val.val x=c*(-deriv (cover (flux ρ u)) x/cover ρ.val.val x)
  rw [(((contDiff_one_iff_deriv.mp (flux_c1 ρ u)).1 x).hasDerivAt.const_mul c).deriv]
  change -(c*deriv (cover (flux ρ u)) x)/cover ρ.val.val x=c*(-deriv (cover (flux ρ u)) x/cover ρ.val.val x)
  ring
theorem laplacian_add (ρ : RegularDensity) (u v : C2Coefficient) :
    laplacian ρ (u+v)=laplacian ρ u+laplacian ρ v := by
  have hn : laplacian ρ (-v) = -laplacian ρ v := by simpa only [show (-1 : ℝ)•v = -v from Subtype.ext (ContinuousMap.ext (fun q => neg_one_mul (v.val q))),neg_one_smul] using laplacian_smul ρ (-1) v
  simpa only [sub_neg_eq_add,hn] using laplacian_sub ρ u (-v)
noncomputable def solution (ρ : RegularDensity) (f : Compatible ρ) : C2Coefficient := green ρ f.val
theorem solution_solves (ρ : RegularDensity) (f : Compatible ρ) : laplacian ρ (solution ρ f)=f.val :=
  (green_solves_projected ρ f.val).trans (project_eq_self ρ f.val f.property)
theorem solution_mean_zero (ρ : RegularDensity) (f : Compatible ρ) : weightedMean ρ (solution ρ f).val=0 := green_mean_zero _ _
theorem solution_add (ρ : RegularDensity) (f g : Compatible ρ) : solution ρ (f+g)=solution ρ f+solution ρ g :=
  normalized_unique ρ _ _ (by rw [solution_solves,laplacian_add,solution_solves,solution_solves];rfl)
    (solution_mean_zero _ _) (by change weightedMean ρ ((solution ρ f).val+(solution ρ g).val)=0;rw [weightedMean_add,solution_mean_zero,solution_mean_zero,add_zero])
theorem solution_smul (ρ : RegularDensity) (c : ℝ) (f : Compatible ρ) : solution ρ (c•f)=c•solution ρ f :=
  normalized_unique ρ _ _ (by rw [solution_solves,laplacian_smul,solution_solves];rfl)
    (solution_mean_zero _ _) (by change weightedMean ρ (c•(solution ρ f).val)=0;rw [weightedMean_smul,solution_mean_zero,mul_zero])
/-- A bounded linear endomorphism of the actual closed C0 forcing subspace, with a C2 image. -/
noncomputable def greenMap (ρ : RegularDensity) : Compatible ρ →L[ℝ] Compatible ρ :=
  LinearMap.mkContinuous
    {toFun:=fun f => ⟨(solution ρ f).val,solution_mean_zero ρ f⟩,
     map_add':=fun f g => Subtype.ext (congrArg (fun u : C2Coefficient => u.val) (solution_add ρ f g)),
     map_smul':=fun c f => Subtype.ext (congrArg (fun u : C2Coefficient => u.val) (solution_smul ρ c f))}
    (4*(mean ρ.val.val)^2) (fun f => green_bound ρ f.val f.property)
theorem greenMap_apply (ρ : RegularDensity) (f : Compatible ρ) : (greenMap ρ f).val=(green ρ f.val).val := rfl
theorem greenMap_regular (ρ : RegularDensity) (f : Compatible ρ) : ContDiff ℝ 2 (cover (greenMap ρ f).val) :=
  (solution ρ f).property
theorem greenMap_right_inverse (ρ : RegularDensity) (f : Compatible ρ) :
    laplacian ρ ⟨(greenMap ρ f).val,greenMap_regular ρ f⟩=f.val := solution_solves ρ f
theorem greenMap_left_inverse (ρ : RegularDensity) (u : C2Coefficient) :
    (greenMap ρ ⟨laplacian ρ u,weightedMean_laplacian ρ u⟩).val=(normalize ρ u).val :=
  congrArg Subtype.val (green_laplacian_eq_normalize ρ u)
theorem greenMap_bound (ρ : RegularDensity) (f : Compatible ρ) :
    ‖greenMap ρ f‖≤4*(mean ρ.val.val)^2*‖f‖ := green_bound ρ f.val f.property
theorem greenMap_injective (ρ : RegularDensity) : Function.Injective (greenMap ρ) :=
  fun f g h => Subtype.ext ((solution_solves ρ f).symm.trans
    ((congrArg (laplacian ρ) (show solution ρ f=solution ρ g from Subtype.ext (congrArg (fun u : Compatible ρ => u.val) h))).trans (solution_solves ρ g)))
theorem greenMap_stability (ρ : RegularDensity) (f g : Compatible ρ) :
    ‖greenMap ρ f-greenMap ρ g‖≤4*(mean ρ.val.val)^2*‖f-g‖ := by
  rw [← map_sub]
  exact green_bound ρ (f-g).val (f-g).property

theorem gradient_constant (c : ℝ) : gradient (constantC2 c)=0 := by
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  exact deriv_const x c
theorem gradient_normalize (ρ : RegularDensity) (u : C2Coefficient) : gradient (normalize ρ u)=gradient u := by
  rw [Poisson.normalize,gradient_sub,gradient_constant,sub_zero]
theorem solution_gradient (ρ : RegularDensity) (f : Compatible ρ) : gradient (solution ρ f)=velocity ρ f.val := by
  rw [solution,green,project_eq_self ρ f.val f.property,gradient_normalize,base_gradient]
theorem greenMap_gradient_bound (ρ : RegularDensity) (f : Compatible ρ) :
    ‖gradient (solution ρ f)‖≤2*mean ρ.val.val*‖ρ.val.val‖*‖f‖ := by
  have hm := (mean_pos ρ.val).le
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro q
  rw [solution_gradient]
  have hp : ρ.val.val q≤‖ρ.val.val‖ := by simpa only [norm_of_positive (ρ.val.property q)] using ρ.val.val.norm_coe_le_norm q
  exact (velocity_point_bound ρ f.val f.property q).trans
    ((mul_le_mul_of_nonneg_left hp (by positivity : 0≤2*mean ρ.val.val*‖f.val‖)).trans_eq (by
      change (2*mean ρ.val.val*‖f.val‖)*‖ρ.val.val‖=2*mean ρ.val.val*‖ρ.val.val‖*‖f.val‖;ring))
theorem greenMap_flux_bound (ρ : RegularDensity) (f : Compatible ρ) :
    ‖flux ρ (solution ρ f)‖≤2*mean ρ.val.val*‖f‖ := by
  have hm := (mean_pos ρ.val).le
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro q
  change ‖gradient (solution ρ f) q/ρ.val.val q‖≤_
  rw [norm_div,norm_of_positive (ρ.val.property q),solution_gradient]
  exact (div_le_iff₀ (ρ.val.property q)).mpr (velocity_point_bound ρ f.val f.property q)
theorem greenMap_gradient_stability (ρ : RegularDensity) (f g : Compatible ρ) :
    ‖gradient (solution ρ f)-gradient (solution ρ g)‖≤2*mean ρ.val.val*‖ρ.val.val‖*‖f-g‖ := by
  have he : solution ρ (f-g)=solution ρ f-solution ρ g := Subtype.ext (congrArg (fun u : Compatible ρ => u.val) (map_sub (greenMap ρ) f g))
  simpa only [he,gradient_sub] using greenMap_gradient_bound ρ (f-g)
/-- Ordinary weighted integral pairing; no Hilbert completion or self-adjoint realization. -/
noncomputable def pairing (ρ : RegularDensity) (f g : Coefficient) : ℝ := mean (ρ.val.val*f*g)
theorem greenMap_pairing_symmetry (ρ : RegularDensity) (f g : Compatible ρ) :
    pairing ρ f.val (greenMap ρ g).val=pairing ρ g.val (greenMap ρ f).val := by
  change (∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover f.val x*cover (solution ρ g).val x)=
    ∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover g.val x*cover (solution ρ f).val x
  calc
    _ = ∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover (solution ρ f).val x*cover g.val x := by
      simpa only [solution_solves] using pairing_symmetry ρ (solution ρ f) (solution ρ g)
    _ = _ := intervalIntegral.integral_congr (fun x _ => by ring)
theorem solution_gradient_nonzero (ρ : RegularDensity) (f : Compatible ρ) (hf : f≠0) :
    ∃ q,gradient (solution ρ f) q≠0 := by
  by_contra h
  have hg : gradient (solution ρ f)=0 := by ext q;exact not_ne_iff.mp (not_exists.mp h q)
  have hc : ∃ c : ℝ,(solution ρ f).val=constant c := by
    refine ⟨cover (solution ρ f).val 0,?_⟩
    ext q
    induction q using Quotient.inductionOn with | _ x =>
    exact is_const_of_deriv_eq_zero ((contDiff_one_iff_deriv.mp (c2_c1 (solution ρ f))).1)
      (fun t => by change gradient (solution ρ f) (t : CircleHodge.Circle)=0;rw [hg];rfl) x 0
  obtain ⟨c,hc⟩:=hc
  exact hf (Subtype.ext ((solution_solves ρ f).symm.trans (laplacian_of_constant ρ _ c hc)))
theorem greenMap_pairing_positive (ρ : RegularDensity) (f : Compatible ρ) (hf : f≠0) :
    0<pairing ρ f.val (greenMap ρ f).val := by
  obtain ⟨q,hq⟩:=solution_gradient_nonzero ρ f hf
  let e : Coefficient := gradient (solution ρ f)*flux ρ (solution ρ f)
  have he (t : CircleHodge.Circle) : e t=gradient (solution ρ f) t*gradient (solution ρ f) t/ρ.val.val t := by
    change gradient (solution ρ f) t*(gradient (solution ρ f) t/ρ.val.val t)=_;ring
  have hp : 0<mean e := by
    rw [mean_circle]
    apply integral_pos_of_integrable_nonneg_nonzero e.continuous (continuous_integrable e.continuous)
      (fun t => by rw [he];exact div_nonneg (mul_self_nonneg _) (ρ.val.property t).le)
    rw [he]
    exact ne_of_gt (div_pos (mul_self_pos.mpr hq) (ρ.val.property q))
  have hi:=green_identity ρ (solution ρ f) (solution ρ f)
  rw [solution_solves] at hi
  change 0<(∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover f.val x*cover (solution ρ f).val x)
  rw [hi]
  have heI : mean e=(∫ x in (0 : ℝ)..1,cover (gradient (solution ρ f)) x*cover (gradient (solution ρ f)) x/cover ρ.val.val x) :=
    intervalIntegral.integral_congr (fun x _ => he (x : CircleHodge.Circle))
  exact heI ▸ hp

theorem greenMap_range_iff (ρ : RegularDensity) (u : Compatible ρ) :
    (∃ f,greenMap ρ f=u) ↔ ContDiff ℝ 2 (cover u.val) := by
  constructor
  · rintro ⟨f,rfl⟩;exact greenMap_regular ρ f
  · intro hu
    let v : C2Coefficient := ⟨u.val,hu⟩
    refine ⟨⟨laplacian ρ v,weightedMean_laplacian ρ v⟩,Subtype.ext ?_⟩
    rw [greenMap_left_inverse]
    have hm : weightedMean ρ u.val=0 := u.property
    change u.val-constant (weightedMean ρ u.val/mean ρ.val.val)=u.val
    rw [hm,zero_div]
    ext q;exact sub_zero _
/-- A concrete nonzero compatible forcing for every admitted density; not a vacuous zero space. -/
noncomputable def exampleForcing (ρ : RegularDensity) : Compatible ρ :=
  ⟨laplacian ρ cosineC2,weightedMean_laplacian ρ cosineC2⟩
theorem exampleForcing_nonzero (ρ : RegularDensity) : exampleForcing ρ≠0 :=
  fun h => cosine_nonconstant ((kernel_iff_constant ρ cosineC2).mp (congrArg (fun f : Compatible ρ => f.val) h))
theorem example_pairing_positive (ρ : RegularDensity) :
    0<pairing ρ (exampleForcing ρ).val (greenMap ρ (exampleForcing ρ)).val :=
  greenMap_pairing_positive ρ (exampleForcing ρ) (exampleForcing_nonzero ρ)

end ComputationalHodge.GreenOperator
