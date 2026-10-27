module
public import Density
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
@[expose] public section
namespace ComputationalHodge.Poisson
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.LoopCharacters
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts ComputationalHodge.MetricHodge
open MeasureTheory Set
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
theorem laplacian_cover (ρ : RegularDensity) (u : C2Coefficient) (x : ℝ) :
    cover (laplacian ρ u) x=-(deriv (fun t => deriv (cover u.val) t/cover ρ.val.val t) x)/cover ρ.val.val x := rfl

noncomputable def weightedMean (ρ : RegularDensity) (f : Coefficient) : ℝ := mean (ρ.val.val*f)
theorem weightedMean_laplacian (ρ : RegularDensity) (u : C2Coefficient) : weightedMean ρ (laplacian ρ u)=0 := by
  apply exact_mean_zero
  refine ⟨-flux ρ u,(flux_c1 ρ u).neg,fun x => ?_⟩
  have hd:=(((contDiff_one_iff_deriv.mp (flux_c1 ρ u)).1 x).hasDerivAt.neg).deriv
  change deriv (-cover (flux ρ u)) x=_
  rw [hd]
  change _=cover ρ.val.val x*(-(deriv (cover (flux ρ u)) x)/cover ρ.val.val x)
  field_simp [show cover ρ.val.val x≠0 from density_ne ρ.val (x : CircleHodge.Circle)]

theorem green_identity (ρ : RegularDensity) (u v : C2Coefficient) :
    (∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover (laplacian ρ u) x*cover v.val x)=
      ∫ x in (0 : ℝ)..1,cover (gradient u) x*cover (gradient v) x/cover ρ.val.val x := by
  have hi:=((flux_c1 ρ u).contDiffOn.absolutelyContinuousOnInterval (a:=0) (b:=1)).integral_mul_deriv_eq_deriv_mul
    ((c2_c1 v).contDiffOn.absolutelyContinuousOnInterval (a:=0) (b:=1))
  have hp:=cover_periodic (flux ρ u) 0
  have hq:=cover_periodic v.val 0
  simp only [zero_add] at hp hq
  rw [hp,hq,sub_self,zero_sub] at hi
  have hl : (fun x => cover ρ.val.val x*cover (laplacian ρ u) x*cover v.val x)=
      fun x => -(deriv (cover (flux ρ u)) x*cover v.val x) := by
    funext x
    change cover ρ.val.val x*(-(deriv (cover (flux ρ u)) x)/cover ρ.val.val x)*cover v.val x=_
    field_simp [show cover ρ.val.val x≠0 from density_ne ρ.val (x : CircleHodge.Circle)]
  have hr : (fun x => cover (gradient u) x*cover (gradient v) x/cover ρ.val.val x)=
      fun x => cover (flux ρ u) x*deriv (cover v.val) x := by
    funext x
    change deriv (cover u.val) x*deriv (cover v.val) x/cover ρ.val.val x=
      (deriv (cover u.val) x/cover ρ.val.val x)*deriv (cover v.val) x
    ring
  rw [hl,hr,intervalIntegral.integral_neg]
  exact hi.symm
theorem pairing_symmetry (ρ : RegularDensity) (u v : C2Coefficient) :
    (∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover (laplacian ρ u) x*cover v.val x)=
      ∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover u.val x*cover (laplacian ρ v) x := by
  rw [green_identity]
  calc
    _ = ∫ x in (0 : ℝ)..1,cover (gradient v) x*cover (gradient u) x/cover ρ.val.val x :=
      intervalIntegral.integral_congr (fun _ _ => by ring)
    _ = ∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover (laplacian ρ v) x*cover u.val x := (green_identity ρ v u).symm
    _ = _ := intervalIntegral.integral_congr (fun _ _ => by ring)
noncomputable def cosine : Coefficient where
  toFun q := (AddCircle.toCircle q : ℂ).re
  continuous_toFun := by fun_prop
theorem cosine_cover (x : ℝ) : cover cosine x=Real.cos (2*Real.pi*x) := by
  change (AddCircle.toCircle (x : CircleHodge.Circle) : ℂ).re=_
  rw [AddCircle.toCircle_apply_mk,Circle.coe_exp]
  norm_num [Complex.exp_re]
noncomputable def cosineC2 : C2Coefficient := ⟨cosine,by
  have he : cover cosine=fun x => Real.cos (2*Real.pi*x) := funext cosine_cover
  change ContDiff ℝ 2 (cover cosine)
  rw [he]
  fun_prop⟩
theorem cosine_zero : cosine 0=1 := by norm_num [cosine]
end ComputationalHodge.Poisson
