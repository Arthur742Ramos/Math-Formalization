module
public import Energy
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Measure.OpenPos
@[expose] public section
namespace ComputationalHodge.MetricHodge
open ComputationalHodge.CircleHodge MeasureTheory Set
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

end ComputationalHodge.MetricHodge
