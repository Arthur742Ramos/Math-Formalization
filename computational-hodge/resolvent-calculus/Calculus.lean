module
public import Positive
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Operator.NormedSpace
@[expose] public section
namespace ComputationalHodge.ResolventCalculus
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson
open ComputationalHodge.GreenOperator ComputationalHodge.PositiveResolvent
open ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals ComputationalHodge.LoopCharacters
open Filter Set
open scoped Topology

/-- The two actual differential shifts differ by a scalar zeroth-order term. -/
theorem positive_shift (ρ : RegularDensity) (κ μ : ℝ) (u : C2Coefficient) :
    positive ρ κ u=positive ρ μ u+(κ-μ)•u.val := by
  ext q
  change laplacian ρ u q+κ*u.val q=(laplacian ρ u q+μ*u.val q)+(κ-μ)*u.val q
  ring

/-- The resolvent identity is derived from actual C2 equations and injectivity. -/
theorem resolvent_identity (ρ : RegularDensity) (κ μ : ℝ) (hκ : 0<κ) (hμ : 0<μ) :
    resolvent ρ κ hκ-resolvent ρ μ hμ=
      (μ-κ)•((resolvent ρ κ hκ).comp (resolvent ρ μ hμ)) := by
  apply ContinuousLinearMap.ext
  intro f
  have he : solve ρ κ hκ f-solve ρ μ hμ f=
      (μ-κ)•solve ρ κ hκ (resolvent ρ μ hμ f) := by
    apply positive_injective ρ κ hκ
    rw [positive_sub,solve_equation,positive_shift ρ κ μ (solve ρ μ hμ f),
      solve_equation,positive_smul,solve_equation]
    ext q
    change f q-(f q+(κ-μ)*(resolvent ρ μ hμ f) q)=(μ-κ)*(resolvent ρ μ hμ f) q
    ring
  exact congrArg Subtype.val he

/-- Commutation includes the equal-parameter case, without dividing by zero. -/
theorem resolvent_commute (ρ : RegularDensity) (κ μ : ℝ) (hκ : 0<κ) (hμ : 0<μ) :
    (resolvent ρ κ hκ).comp (resolvent ρ μ hμ)=
      (resolvent ρ μ hμ).comp (resolvent ρ κ hκ) := by
  by_cases h : κ=μ
  · subst μ; rfl
  apply smul_right_injective (Coefficient →L[ℝ] Coefficient) (sub_ne_zero.mpr (Ne.symm h))
  calc
    (μ-κ)•((resolvent ρ κ hκ).comp (resolvent ρ μ hμ)) =
        resolvent ρ κ hκ-resolvent ρ μ hμ := (resolvent_identity ρ κ μ hκ hμ).symm
    _ = -(resolvent ρ μ hμ-resolvent ρ κ hκ) := by simp only [neg_sub]
    _ = -((κ-μ)•((resolvent ρ μ hμ).comp (resolvent ρ κ hκ))) :=
      congrArg Neg.neg (resolvent_identity ρ μ κ hμ hκ)
    _ = (μ-κ)•((resolvent ρ μ hμ).comp (resolvent ρ κ hκ)) :=
      (neg_smul (κ-μ) _).symm.trans (congrArg (fun c : ℝ => c • _) (neg_sub κ μ))

/-- A genuine operator-norm bound, proved from the pointwise forcing estimate. -/
theorem resolvent_opNorm (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) :
    ‖resolvent ρ κ hκ‖≤κ⁻¹ := by
  exact LinearMap.mkContinuous_norm_le _ (inv_nonneg.mpr hκ.le) _

theorem comp_bound (ρ : RegularDensity) (κ μ : ℝ) (hκ : 0<κ) (hμ : 0<μ) :
    ‖(resolvent ρ κ hκ).comp (resolvent ρ μ hμ)‖≤κ⁻¹*μ⁻¹ :=
  ((resolvent ρ κ hκ).opNorm_comp_le (resolvent ρ μ hμ)).trans
    (mul_le_mul (resolvent_opNorm ρ κ hκ) (resolvent_opNorm ρ μ hμ)
      (norm_nonneg _) (inv_nonneg.mpr hκ.le))

/-- The actual C0 operator-norm difference estimate for all positive parameters. -/
theorem resolvent_difference_bound (ρ : RegularDensity) (κ μ : ℝ) (hκ : 0<κ) (hμ : 0<μ) :
    ‖resolvent ρ κ hκ-resolvent ρ μ hμ‖≤|κ-μ|/(κ*μ) := by
  have hb := (ContinuousLinearMap.opNorm_smul_le (μ-κ)
      ((resolvent ρ κ hκ).comp (resolvent ρ μ hμ))).trans
    (mul_le_mul_of_nonneg_left (comp_bound ρ κ μ hκ hμ) (norm_nonneg (μ-κ)))
  calc
    ‖resolvent ρ κ hκ-resolvent ρ μ hμ‖ ≤ ‖μ-κ‖*(κ⁻¹*μ⁻¹) := by
      rw [resolvent_identity]; exact hb
    _ = |κ-μ|/(κ*μ) := by rw [Real.norm_eq_abs,abs_sub_comm]; field_simp [hκ.ne',hμ.ne']

/-- A total family for real-parameter differentiation; no regularity is claimed outside κ>0. -/
noncomputable def family (ρ : RegularDensity) (κ : ℝ) : Coefficient →L[ℝ] Coefficient :=
  if hκ : 0<κ then resolvent ρ κ hκ else 0

theorem family_of_pos (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) :
    family ρ κ=resolvent ρ κ hκ := dite_eq_left hκ

/-- Uniform operator-norm Lipschitz control on every positive half-line. -/
theorem resolvent_uniform_lipschitz (ρ : RegularDensity) (a κ μ : ℝ)
    (ha : 0<a) (hκ : 0<κ) (hμ : 0<μ) (hκa : a≤κ) (hμa : a≤μ) :
    ‖resolvent ρ κ hκ-resolvent ρ μ hμ‖≤|κ-μ| *(a⁻¹*a⁻¹) := by
  have hden : a*a≤κ*μ := mul_le_mul hκa hμa ha.le hκ.le
  calc
    ‖resolvent ρ κ hκ-resolvent ρ μ hμ‖≤|κ-μ|/(κ*μ) :=
      resolvent_difference_bound ρ κ μ hκ hμ
    _ ≤ |κ-μ|/(a*a) := div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos ha ha) hden
    _ = |κ-μ| *(a⁻¹*a⁻¹) := by rw [div_eq_mul_inv,mul_inv_rev]

section OperatorDerivative
attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
attribute [local instance 1001] NormedSpace.toModule PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

/-- The actual positive resolvent varies continuously in the C0 operator norm. -/
theorem family_continuousAt (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) :
    ContinuousAt (family ρ) κ := by
  have hb : ∀ᶠ μ in 𝓝 κ,
      ‖family ρ μ-family ρ κ‖≤|μ-κ| *((κ/2)⁻¹*(κ/2)⁻¹) := by
    filter_upwards [lt_mem_nhds (show κ/2<κ by linarith)] with μ hm
    have hμ : 0<μ := (half_pos hκ).trans hm
    rw [family_of_pos ρ μ hμ,family_of_pos ρ κ hκ]
    exact resolvent_uniform_lipschitz ρ (κ/2) μ κ (half_pos hκ) hμ hκ hm.le (by linarith)
  have hz : Tendsto (fun μ : ℝ => |μ-κ| *((κ/2)⁻¹*(κ/2)⁻¹)) (𝓝 κ) (𝓝 0) := by
    simpa only [Pi.sub_apply,id_eq,sub_self,abs_zero,zero_mul] using
      (((continuous_id : Continuous (fun μ : ℝ => μ)).sub
        (continuous_const : Continuous (fun _ : ℝ => κ))).abs.mul_const ((κ/2)⁻¹*(κ/2)⁻¹)).tendsto κ
  apply tendsto_sub_nhds_zero_iff.mp
  with_reducible_and_instances
    exact squeeze_zero_norm' (f := fun μ : ℝ => family ρ μ-family ρ κ) hb hz

/-- Operator-norm derivative at every strictly positive real shift. -/
theorem family_hasDerivAt (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) :
    HasDerivAt (family ρ) (-((resolvent ρ κ hκ).comp (resolvent ρ κ hκ))) κ := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have ht := (((family_continuousAt ρ κ hκ).clm_comp
    (continuousAt_const : ContinuousAt (fun _ : ℝ => family ρ κ) κ)).neg).mono_left (nhdsWithin_le_nhds (s := {κ}ᶜ))
  simp only [Pi.neg_apply,family_of_pos ρ κ hκ] at ht
  apply ht.congr'
  filter_upwards [(lt_mem_nhds hκ).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with μ hμ hn
  have hne : μ-κ≠0 := sub_ne_zero.mpr (by simpa only [mem_compl_iff,mem_singleton_iff] using hn)
  have hcoef : (μ-κ)⁻¹*(κ-μ)=(-1:ℝ) := by
    rw [show κ-μ=-(μ-κ) by ring, mul_neg,inv_mul_cancel₀ hne]
  simp only [Pi.neg_apply,slope_def_module,family_of_pos ρ μ hμ,family_of_pos ρ κ hκ,
    resolvent_identity ρ μ κ hμ hκ,smul_smul,hcoef]
  with_reducible_and_instances
    simpa only [one_smul] using (neg_smul (1 : ℝ) ((resolvent ρ μ hμ).comp (resolvent ρ κ hκ))).symm

end OperatorDerivative

/-- Actual raw loop periods of the positive resolvent scale by the reciprocal shift. -/
theorem raw_period (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) (p : Trace 0 0) :
    lineIntegral (ρ.val.val*resolvent ρ κ hκ f) (fromTrace p)=
      κ⁻¹*lineIntegral (ρ.val.val*f) (fromTrace p) := by
  rw [lineIntegral_eq_mean,lineIntegral_eq_mean]
  change weightedMean ρ (resolvent ρ κ hκ f)*_=κ⁻¹*(weightedMean ρ f*_)
  rw [resolvent_weightedMean,div_eq_mul_inv]
  ring

/-- The derivative is for the literal weighted integral along each actual based loop. -/
theorem raw_period_hasDerivAt (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ)
    (f : Coefficient) (p : Trace 0 0) :
    HasDerivAt (fun t : ℝ => lineIntegral (ρ.val.val*family ρ t f) (fromTrace p))
      (-(κ^2)⁻¹*lineIntegral (ρ.val.val*f) (fromTrace p)) κ := by
  apply ((hasDerivAt_inv hκ.ne').mul_const (lineIntegral (ρ.val.val*f) (fromTrace p))).congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hκ] with μ hμ
  rw [family_of_pos ρ μ hμ,raw_period ρ μ hμ f p]

/-- The same sensitivity is proved for the actual finite harmonic-cochain period. -/
theorem cochain_period_hasDerivAt (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ)
    (f : Coefficient) (p : Trace 0 0) :
    HasDerivAt (fun t : ℝ => period p (meanHarmonic (ρ.val.val*family ρ t f)))
      (-(κ^2)⁻¹*period p (meanHarmonic (ρ.val.val*f))) κ := by
  simpa only [lineIntegral_fromTrace_harmonic] using raw_period_hasDerivAt ρ κ hκ f p

end ComputationalHodge.ResolventCalculus
