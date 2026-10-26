module
public import Density
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
@[expose] public section
namespace ComputationalHodge.Poisson
open ComputationalPaths.Path.GeometricTopology ComputationalHodge.CircleHodge ComputationalHodge.LoopCharacters ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts ComputationalHodge.MetricHodge MeasureTheory Set
open scoped Topology NNReal unitInterval ContDiff

/-- Positive C¹ length density, in the coordinate convention ds=ρ dx. -/
abbrev RegularDensity := {ρ : Density // ContDiff ℝ 1 (cover ρ.val)}
/-- Actual C² circle functions, not arbitrary real functions with totalized derivatives. -/
def C2Space : Submodule ℝ Coefficient where
  carrier := {u | ContDiff ℝ 2 (cover u)}
  zero_mem' := by change ContDiff ℝ 2 (fun _ : ℝ => 0);exact contDiff_const
  add_mem' := by intro u v hu hv;change ContDiff ℝ 2 (cover u) at hu;change ContDiff ℝ 2 (cover v) at hv;exact hu.add hv
  smul_mem' := by intro c u hu;change ContDiff ℝ 2 (cover u) at hu;exact hu.const_smul c
abbrev C2Coefficient := ↥C2Space

theorem c2_c1 (u : C2Coefficient) : ContDiff ℝ 1 (cover u.val) :=
  (show ContDiff ℝ 2 (cover u.val) from u.property).of_le (by norm_num)
theorem c2_deriv_c1 (u : C2Coefficient) : ContDiff ℝ 1 (deriv (cover u.val)) :=
  (contDiff_succ_iff_deriv.mp (show ContDiff ℝ ((1 : ℕ∞ω)+1) (cover u.val) from u.property)).2.2
theorem periodic_deriv {f : ℝ→ℝ} (hp : Function.Periodic f 1) (hd : Differentiable ℝ f) :
    Function.Periodic (deriv f) 1 := by
  intro x
  have he : (fun y => f (y+1))=f := funext hp
  have h:=((hd (x+1)).hasDerivAt.comp x ((hasDerivAt_id x).add_const 1)).deriv
  change deriv (fun y => f (y+1)) x=deriv f (x+1)*1 at h
  rw [he] at h
  simpa only [mul_one] using h.symm
noncomputable def derivativeCoefficient (f : Coefficient) (hf : ContDiff ℝ 1 (cover f)) : Coefficient where
  toFun := (periodic_deriv (cover_periodic f) (contDiff_one_iff_deriv.mp hf).1).lift
  continuous_toFun := (contDiff_one_iff_deriv.mp hf).2.quotient_liftOn' _
noncomputable def gradient (u : C2Coefficient) : Coefficient := derivativeCoefficient u.val (c2_c1 u)
noncomputable def flux (ρ : RegularDensity) (u : C2Coefficient) : Coefficient where
  toFun q := gradient u q/ρ.val.val q
  continuous_toFun := (gradient u).continuous.div ρ.val.val.continuous (density_ne ρ.val)
theorem flux_c1 (ρ : RegularDensity) (u : C2Coefficient) : ContDiff ℝ 1 (cover (flux ρ u)) :=
  (c2_deriv_c1 u).div ρ.property (fun x => density_ne ρ.val (x : CircleHodge.Circle))
/-- The actual continuous circle Laplacian δd, with the nonnegative geometer's sign. -/
noncomputable def laplacian (ρ : RegularDensity) (u : C2Coefficient) : Coefficient where
  toFun q := -(derivativeCoefficient (flux ρ u) (flux_c1 ρ u) q)/ρ.val.val q
  continuous_toFun := (derivativeCoefficient (flux ρ u) (flux_c1 ρ u)).continuous.neg.div
    ρ.val.val.continuous (density_ne ρ.val)

noncomputable def weightedMean (ρ : RegularDensity) (f : Coefficient) : ℝ := mean (ρ.val.val*f)
theorem weightedMean_sub (ρ : RegularDensity) (f g : Coefficient) :
    weightedMean ρ (f-g)=weightedMean ρ f-weightedMean ρ g := by
  unfold weightedMean
  rw [mul_sub,mean_sub]
theorem weightedMean_constant (ρ : RegularDensity) (c : ℝ) :
    weightedMean ρ (constant c)=c*mean ρ.val.val := by
  have he : ρ.val.val*constant c=c•ρ.val.val := by ext q;change _*c=c*_;ring
  rw [weightedMean,he,mean_smul]
noncomputable def constantC2 (c : ℝ) : C2Coefficient := ⟨constant c,by change ContDiff ℝ 2 (fun _ : ℝ => c);exact contDiff_const⟩

theorem gradient_sub (u v : C2Coefficient) : gradient (u-v)=gradient u-gradient v := ContinuousMap.ext fun q => Quotient.inductionOn q fun x =>
  deriv_sub ((contDiff_one_iff_deriv.mp (c2_c1 u)).1 x) ((contDiff_one_iff_deriv.mp (c2_c1 v)).1 x)

theorem flux_sub (ρ : RegularDensity) (u v : C2Coefficient) : flux ρ (u-v)=flux ρ u-flux ρ v := ContinuousMap.ext fun q =>
  (congrArg (fun f : Coefficient => f q/ρ.val.val q) (gradient_sub u v)).trans (sub_div _ _ _)

theorem laplacian_sub (ρ : RegularDensity) (u v : C2Coefficient) :
    laplacian ρ (u-v)=laplacian ρ u-laplacian ρ v := by
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change -(deriv (cover (flux ρ (u-v))) x)/cover ρ.val.val x=_
  rw [flux_sub]
  change -(deriv (cover (flux ρ u)-cover (flux ρ v)) x)/cover ρ.val.val x=_
  rw [deriv_sub ((contDiff_one_iff_deriv.mp (flux_c1 ρ u)).1 x)
    ((contDiff_one_iff_deriv.mp (flux_c1 ρ v)).1 x)]
  change _=-(deriv (cover (flux ρ u)) x)/cover ρ.val.val x-(-(deriv (cover (flux ρ v)) x)/cover ρ.val.val x)
  ring
theorem laplacian_of_constant (ρ : RegularDensity) (u : C2Coefficient) (c : ℝ) (hu : u.val=constant c) :
    laplacian ρ u=0 := by
  have hg : gradient u=0 := ContinuousMap.ext fun q => Quotient.inductionOn q fun x =>
    (congrArg (fun f : Coefficient => deriv (cover f) x) hu).trans (deriv_const x c)
  have hf : flux ρ u=0 := ContinuousMap.ext fun q =>
    (congrArg (fun f : Coefficient => f q/ρ.val.val q) hg).trans (zero_div _)
  exact ContinuousMap.ext fun q => Quotient.inductionOn q fun x => by
    change -(deriv (cover (flux ρ u)) x)/cover ρ.val.val x=0
    rw [hf]
    change -(deriv (fun _ : ℝ => (0 : ℝ)) x)/cover ρ.val.val x=0
    simp only [deriv_const,neg_zero,zero_div]

theorem weightedMean_laplacian (ρ : RegularDensity) (u : C2Coefficient) : weightedMean ρ (laplacian ρ u)=0 := by
  apply exact_mean_zero
  refine ⟨-flux ρ u,(flux_c1 ρ u).neg,fun x => ?_⟩
  have hd:=(((contDiff_one_iff_deriv.mp (flux_c1 ρ u)).1 x).hasDerivAt.neg).deriv
  change deriv (-cover (flux ρ u)) x=_
  rw [hd]
  change _=cover ρ.val.val x*(-(deriv (cover (flux ρ u)) x)/cover ρ.val.val x)
  field_simp [show cover ρ.val.val x≠0 from density_ne ρ.val (x : CircleHodge.Circle)]

theorem kernel_iff_constant (ρ : RegularDensity) (u : C2Coefficient) :
    laplacian ρ u=0 ↔ ∃ c : ℝ,u.val=constant c := by
  constructor
  · intro he
    have hz (x : ℝ) : deriv (cover (flux ρ u)) x=0 := by
      have h:=congrArg (fun f : Coefficient => cover f x) he
      change -(deriv (cover (flux ρ u)) x)/cover ρ.val.val x=0 at h
      exact neg_eq_zero.mp ((div_eq_zero_iff.mp h).resolve_right (density_ne ρ.val (x : CircleHodge.Circle)))
    have hc (x : ℝ) : cover (flux ρ u) x=cover (flux ρ u) 0 :=
      is_const_of_deriv_eq_zero (contDiff_one_iff_deriv.mp (flux_c1 ρ u)).1 hz x 0
    have hg : gradient u=(cover (flux ρ u) 0)•ρ.val.val := by
      ext q
      induction q using Quotient.inductionOn with | _ x =>
      exact (div_eq_iff (density_ne ρ.val (x : CircleHodge.Circle))).mp (hc x)
    have hm : mean (gradient u)=0 := exact_mean_zero ⟨u.val,c2_c1 u,fun _ => rfl⟩
    rw [hg,mean_smul] at hm
    have h0 : cover (flux ρ u) 0=0 := (mul_eq_zero.mp hm).resolve_right (ne_of_gt (mean_pos ρ.val))
    have hd (x : ℝ) : deriv (cover u.val) x=0 :=
      (congrArg (fun f : Coefficient => cover f x) hg).trans (by rw [h0,zero_smul];rfl)
    refine ⟨cover u.val 0,?_⟩
    ext q
    induction q using Quotient.inductionOn with | _ x =>
    exact is_const_of_deriv_eq_zero (contDiff_one_iff_deriv.mp (c2_c1 u)).1 hd x 0
  · rintro ⟨c,hc⟩;exact laplacian_of_constant ρ u c hc

theorem green_identity (ρ : RegularDensity) (u v : C2Coefficient) :
    (∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover (laplacian ρ u) x*cover v.val x)=
      ∫ x in (0 : ℝ)..1,cover (gradient u) x*cover (gradient v) x/cover ρ.val.val x := by
  have hi:=((flux_c1 ρ u).contDiffOn.absolutelyContinuousOnInterval (a:=0) (b:=1)).integral_mul_deriv_eq_deriv_mul
    ((c2_c1 v).contDiffOn.absolutelyContinuousOnInterval (a:=0) (b:=1))
  have hp:=cover_periodic (flux ρ u) 0
  have hq:=cover_periodic v.val 0
  simp only [zero_add] at hp hq
  rw [hp,hq,sub_self,zero_sub] at hi
  calc
    _ = ∫ x in (0 : ℝ)..1,-(deriv (cover (flux ρ u)) x*cover v.val x) :=
      intervalIntegral.integral_congr (fun x _ => by
        change cover ρ.val.val x*(-(deriv (cover (flux ρ u)) x)/cover ρ.val.val x)*cover v.val x=_
        field_simp [show cover ρ.val.val x≠0 from density_ne ρ.val (x : CircleHodge.Circle)])
    _ = _ := intervalIntegral.integral_neg.trans (hi.symm.trans
      (intervalIntegral.integral_congr (fun x _ => by
        change (deriv (cover u.val) x/cover ρ.val.val x)*deriv (cover v.val) x=deriv (cover u.val) x*deriv (cover v.val) x/cover ρ.val.val x
        ring)))

noncomputable def potentialC2 (β : Coefficient) (hβ : ContDiff ℝ 1 (cover β)) : C2Coefficient := ⟨potential β,by
  change ContDiff ℝ ((1 : ℕ∞ω)+1) (cover (potential β))
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨(contDiff_one_iff_deriv.mp (potential_contDiff β)).1,by intro h;norm_num at h,?_⟩
  have he : deriv (cover (potential β))=fun x => cover β x-mean β := funext (potential_deriv β)
  rw [he]
  exact hβ.sub contDiff_const⟩
noncomputable def normalize (ρ : RegularDensity) (u : C2Coefficient) : C2Coefficient :=
  u-constantC2 (weightedMean ρ u.val/mean ρ.val.val)
theorem normalize_mean_zero (ρ : RegularDensity) (u : C2Coefficient) : weightedMean ρ (normalize ρ u).val=0 := by
  change weightedMean ρ (u.val-constant (weightedMean ρ u.val/mean ρ.val.val))=0
  rw [weightedMean_sub,weightedMean_constant,div_mul_cancel₀ _ (ne_of_gt (mean_pos ρ.val)),sub_self]
theorem normalize_laplacian (ρ : RegularDensity) (u : C2Coefficient) : laplacian ρ (normalize ρ u)=laplacian ρ u := by
  rw [normalize,laplacian_sub,laplacian_of_constant ρ (constantC2 (weightedMean ρ u.val/mean ρ.val.val)) _ rfl,sub_zero]
noncomputable def projectForcing (ρ : RegularDensity) (f : Coefficient) : Coefficient :=
  f-constant (weightedMean ρ f/mean ρ.val.val)
theorem project_mean_zero (ρ : RegularDensity) (f : Coefficient) : weightedMean ρ (projectForcing ρ f)=0 := by
  rw [projectForcing,weightedMean_sub,weightedMean_constant,div_mul_cancel₀ _ (ne_of_gt (mean_pos ρ.val)),sub_self]
theorem project_eq_self (ρ : RegularDensity) (f : Coefficient) (h : weightedMean ρ f=0) : projectForcing ρ f=f := by
  ext q
  simp [projectForcing,constant,h]
noncomputable def firstPrimitive (ρ : RegularDensity) (f : Coefficient) : Coefficient := potential (ρ.val.val*f)
noncomputable def fluxConstant (ρ : RegularDensity) (f : Coefficient) : ℝ :=
  weightedMean ρ (firstPrimitive ρ f)/mean ρ.val.val
noncomputable def velocity (ρ : RegularDensity) (f : Coefficient) : Coefficient :=
  ρ.val.val*(constant (fluxConstant ρ f)-firstPrimitive ρ f)
theorem velocity_mean_zero (ρ : RegularDensity) (f : Coefficient) : mean (velocity ρ f)=0 := by
  change weightedMean ρ (constant (fluxConstant ρ f)-firstPrimitive ρ f)=0
  rw [weightedMean_sub,weightedMean_constant,fluxConstant,div_mul_cancel₀ _ (ne_of_gt (mean_pos ρ.val)),sub_self]
theorem velocity_c1 (ρ : RegularDensity) (f : Coefficient) : ContDiff ℝ 1 (cover (velocity ρ f)) :=
  ρ.property.mul (contDiff_const.sub (potential_contDiff (ρ.val.val*f)))
noncomputable def baseSolution (ρ : RegularDensity) (f : Coefficient) : C2Coefficient :=
  potentialC2 (velocity ρ f) (velocity_c1 ρ f)
theorem base_gradient (ρ : RegularDensity) (f : Coefficient) : gradient (baseSolution ρ f)=velocity ρ f := by
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change deriv (cover (potential (velocity ρ f))) x=cover (velocity ρ f) x
  simpa only [velocity_mean_zero,sub_zero] using potential_deriv (velocity ρ f) x
theorem base_flux (ρ : RegularDensity) (f : Coefficient) :
    flux ρ (baseSolution ρ f)=constant (fluxConstant ρ f)-firstPrimitive ρ f := by
  ext q
  change gradient (baseSolution ρ f) q/ρ.val.val q=fluxConstant ρ f-firstPrimitive ρ f q
  rw [base_gradient]
  change (ρ.val.val q*(fluxConstant ρ f-firstPrimitive ρ f q))/ρ.val.val q=_
  exact mul_div_cancel_left₀ _ (density_ne ρ.val q)
theorem firstPrimitive_hasDerivAt (ρ : RegularDensity) (f : Coefficient) (x : ℝ) :
    HasDerivAt (cover (firstPrimitive ρ f))
      (cover ρ.val.val x*cover f x-weightedMean ρ f) x := realPotential_hasDerivAt (ρ.val.val*f) x
theorem base_solves (ρ : RegularDensity) (f : Coefficient) (h : weightedMean ρ f=0) : laplacian ρ (baseSolution ρ f)=f := by
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change -(deriv (cover (flux ρ (baseSolution ρ f))) x)/cover ρ.val.val x=cover f x
  rw [base_flux]
  change -(deriv ((fun _ : ℝ => fluxConstant ρ f)-cover (firstPrimitive ρ f)) x)/cover ρ.val.val x=cover f x
  rw [((hasDerivAt_const x (fluxConstant ρ f)).sub (firstPrimitive_hasDerivAt ρ f x)).deriv,h]
  simp only [sub_zero,zero_sub,neg_neg]
  exact mul_div_cancel_left₀ _ (density_ne ρ.val (x : CircleHodge.Circle))
/-- Constructed normalized Green solution to the forcing with its weighted constant projection removed. -/
noncomputable def green (ρ : RegularDensity) (f : Coefficient) : C2Coefficient :=
  normalize ρ (baseSolution ρ (projectForcing ρ f))
theorem green_solves_projected (ρ : RegularDensity) (f : Coefficient) : laplacian ρ (green ρ f)=projectForcing ρ f := by
  rw [green,normalize_laplacian]
  exact base_solves ρ _ (project_mean_zero ρ f)
theorem green_mean_zero (ρ : RegularDensity) (f : Coefficient) : weightedMean ρ (green ρ f).val=0 := normalize_mean_zero _ _
theorem solutions_differ_constant (ρ : RegularDensity) (u v : C2Coefficient) :
    laplacian ρ u=laplacian ρ v ↔ ∃ c : ℝ,u.val-v.val=constant c := by
  change laplacian ρ u=laplacian ρ v ↔ ∃ c : ℝ,(u-v).val=constant c
  rw [← sub_eq_zero,← laplacian_sub,kernel_iff_constant]
theorem normalized_unique (ρ : RegularDensity) (u v : C2Coefficient)
    (he : laplacian ρ u=laplacian ρ v) (hu : weightedMean ρ u.val=0) (hv : weightedMean ρ v.val=0) : u=v := by
  obtain ⟨c,hc⟩:=(solutions_differ_constant ρ u v).mp he
  have hm : c*mean ρ.val.val=0 := by
    simpa only [weightedMean_sub,hu,hv,sub_self,weightedMean_constant] using (congrArg (weightedMean ρ) hc).symm
  exact Subtype.ext (sub_eq_zero.mp (hc.trans (by rw [(mul_eq_zero.mp hm).resolve_right (ne_of_gt (mean_pos ρ.val))];rfl)))

theorem pairing_symmetry (ρ : RegularDensity) (u v : C2Coefficient) :
    (∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover (laplacian ρ u) x*cover v.val x)=
      ∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover u.val x*cover (laplacian ρ v) x := by
  rw [green_identity]
  calc
    _ = ∫ x in (0 : ℝ)..1,cover (gradient v) x*cover (gradient u) x/cover ρ.val.val x :=
      intervalIntegral.integral_congr (fun _ _ => by ring)
    _ = ∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover (laplacian ρ v) x*cover u.val x := (green_identity ρ v u).symm
    _ = _ := intervalIntegral.integral_congr (fun _ _ => by ring)
end ComputationalHodge.Poisson
