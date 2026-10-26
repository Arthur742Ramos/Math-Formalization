module
public import Range
@[expose] public section
namespace ComputationalHodge.FullCircleRange
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson ComputationalHodge.GreenOperator ComputationalHodge.CompactGreen ComputationalHodge.CircleFredholm ComputationalHodge.ResonanceObstruction ComputationalHodge.ResonantRange ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals MeasureTheory Set
open scoped Topology NNReal unitInterval ContDiff

/-- Actual geometer-sign operator on all C2 coefficients, without normalization. -/
noncomputable def fullShifted (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) : Coefficient :=
  laplacian ρ u-μ•u.val
theorem fullShifted_domain (ρ : RegularDensity) (μ : ℝ) (u : Domain ρ) :
    fullShifted ρ μ u.val=shifted ρ μ u := rfl
theorem fullShifted_sub (ρ : RegularDensity) (μ : ℝ) (u v : C2Coefficient) :
    fullShifted ρ μ (u-v)=fullShifted ρ μ u-fullShifted ρ μ v := (congrArg₂ (·-·) (laplacian_sub ρ u v) (smul_sub μ u.val v.val)).trans
    (sub_sub_sub_comm _ _ _ _)
theorem fullShifted_constant (ρ : RegularDensity) (μ c : ℝ) :
    fullShifted ρ μ (constantC2 c)=constant (-μ*c) := by
  rw [fullShifted,laplacian_of_constant ρ (constantC2 c) c rfl]
  ext q
  change (0 : ℝ)-μ*c=(-μ)*c
  ring
theorem weightedMean_fullShifted (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) :
    weightedMean ρ (fullShifted ρ μ u)= -μ*weightedMean ρ u.val := by
  rw [fullShifted,weightedMean_sub,weightedMean_laplacian,weightedMean_smul]
  ring
theorem nonzero_homogeneous_normalized (ρ : RegularDensity) (μ : ℝ) (hμ : μ≠0)
    (v : C2Coefficient) (hv : fullShifted ρ μ v=0) : weightedMean ρ v.val=0 := by
  exact (mul_eq_zero.mp ((weightedMean_fullShifted ρ μ v).symm.trans
    ((congrArg (meanFunctional ρ) hv).trans (map_zero _)))).resolve_left (neg_ne_zero.mpr hμ)
theorem pairing_constant_left (ρ : RegularDensity) (a : ℝ) (v : Coefficient) :
    pairing ρ (constant a) v=a*weightedMean ρ v := by
  have h : ρ.val.val*constant a*v=a•(ρ.val.val*v) := by ext q;change _*a*_ = a*(_*_);ring
  change mean (ρ.val.val*constant a*v)=a*mean (ρ.val.val*v)
  rw [h,mean_smul]
theorem pairing_one_right (ρ : RegularDensity) (f : Coefficient) :
    pairing ρ f (constant 1)=weightedMean ρ f := by
  rw [pairing_comm,pairing_constant_left,one_mul]
theorem pairing_project (ρ : RegularDensity) (f v : Coefficient) :
    pairing ρ (projectForcing ρ f) v=pairing ρ f v-
      (weightedMean ρ f/mean ρ.val.val)*weightedMean ρ v := by
  rw [projectForcing,pairing_sub_left,pairing_constant_left]
/-- Normalization and the actual shifted operator commute with forcing projection. -/
theorem normalization_commutes (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) :
    fullShifted ρ μ (normalize ρ u)=projectForcing ρ (fullShifted ρ μ u) := by
  rw [Poisson.normalize,fullShifted_sub,fullShifted_constant,projectForcing,weightedMean_fullShifted,mul_div_assoc]
/-- Reconstruct the unrestricted equation with the correct constant-sector sign. -/
theorem reconstruct (ρ : RegularDensity) (μ : ℝ) (hμ : μ≠0) (f : Coefficient)
    (u : C2Coefficient) (hu : fullShifted ρ μ u=projectForcing ρ f) :
    fullShifted ρ μ (u-constantC2 ((weightedMean ρ f/mean ρ.val.val)/μ))=f := by
  rw [fullShifted_sub,hu,fullShifted_constant]
  ext q
  let a:=weightedMean ρ f/mean ρ.val.val
  change f q-a-(-μ*(a/μ))=f q
  have hc : μ*(a/μ)=a := by rw [mul_comm,div_mul_cancel₀ _ hμ]
  rw [neg_mul,hc]
  ring
theorem projected_mode_orthogonal (ρ : RegularDensity) (μ : ℝ) (f : Coefficient)
    (hf : ∀ v : C2Coefficient,fullShifted ρ μ v=0 → pairing ρ f v.val=0)
    (v : Domain ρ) (hv : shifted ρ μ v=0) : pairing ρ (projectForcing ρ f) v.val.val=0 := by
  rw [pairing_project,v.property,mul_zero,sub_zero]
  exact hf v.val hv
theorem solve_nonzero (ρ : RegularDensity) (μ : ℝ) (hμ : μ≠0) (f : Coefficient)
    (hf : ∀ v : C2Coefficient,fullShifted ρ μ v=0 → pairing ρ f v.val=0) :
    ∃ u : C2Coefficient,fullShifted ρ μ u=f := by
  let g : Compatible ρ := ⟨projectForcing ρ f,project_mean_zero ρ f⟩
  obtain ⟨u,hu⟩ := solve_orthogonal ρ μ g
    (modes_imply_orthogonal ρ μ g (projected_mode_orthogonal ρ μ f hf))
  exact ⟨u.val-constantC2 ((weightedMean ρ f/mean ρ.val.val)/μ),reconstruct ρ μ hμ f u.val hu⟩
theorem zero_solvable_iff_raw (ρ : RegularDensity) (f : Coefficient) :
    (∃ u : C2Coefficient,fullShifted ρ 0 u=f) ↔
      ∀ p : Trace 0 0,lineIntegral (ρ.val.val*f) (fromTrace p)=0 := ⟨fun ⟨u,hu⟩ => (compatible_iff_raw ρ f).mp
    (by change weightedMean ρ f=0;rw [← hu,weightedMean_fullShifted,neg_zero,zero_mul]),
   fun hp => let g : Compatible ρ := ⟨f,(compatible_iff_raw ρ f).mpr hp⟩
     ⟨solution ρ g,by simpa only [fullShifted,zero_smul,sub_zero] using solution_solves ρ g⟩⟩
/-- Full actual C2 Fredholm range, with every homogeneous C2 competitor quantified. -/
theorem solvable_iff_modes (ρ : RegularDensity) (μ : ℝ) (f : Coefficient) :
    (∃ u : C2Coefficient,fullShifted ρ μ u=f) ↔
      ∀ v : C2Coefficient,fullShifted ρ μ v=0 → pairing ρ f v.val=0 := by
  constructor
  · rintro ⟨u,hu⟩ v hv
    exact forcing_orthogonal ρ μ u v f (sub_eq_zero.mp hv) hu
  · intro hf
    by_cases hμ : μ=0
    · subst μ
      have hc : fullShifted ρ 0 (constantC2 1)=0 := by rw [fullShifted_constant];ext q;simp [constant]
      have hm : weightedMean ρ f=0 := by simpa only [Poisson.constantC2,pairing_one_right] using hf (constantC2 1) hc
      exact (zero_solvable_iff_raw ρ f).mpr ((compatible_iff_raw ρ f).mp hm)
    · exact solve_nonzero ρ μ hμ f hf
theorem zero_solvable_iff_cochain (ρ : RegularDensity) (f : Coefficient) :
    (∃ u : C2Coefficient,fullShifted ρ 0 u=f) ↔
      ∀ p : Trace 0 0,period p (meanHarmonic (ρ.val.val*f)).val=0 := (zero_solvable_iff_raw ρ f).trans (by simp only [lineIntegral_fromTrace_harmonic])
theorem constant_solution (ρ : RegularDensity) (μ : ℝ) (hμ : μ≠0) :
    fullShifted ρ μ (constantC2 (-1/μ))=constant 1 := by
  rw [fullShifted_constant]
  ext q
  change -μ*(-1/μ)=1
  field_simp [hμ]
theorem constant_unit_period_positive (ρ : RegularDensity) :
    0<lineIntegral (ρ.val.val*constant 1) (fromTrace unitTrace) := by
  simpa only [lineIntegral_unit,show constant 1=(1 : Coefficient) from rfl,mul_one] using mean_pos ρ.val
/-- Off zero, genuine nonzero trace periods do not preclude an actual C2 solution. -/
theorem off_zero_periods_not_necessary (ρ : RegularDensity) (μ : ℝ) (hμ : μ≠0) :
    (∃ u : C2Coefficient,fullShifted ρ μ u=constant 1) ∧
      0<lineIntegral (ρ.val.val*constant 1) (fromTrace unitTrace) :=
  ⟨⟨constantC2 (-1/μ),constant_solution ρ μ hμ⟩,constant_unit_period_positive ρ⟩
end ComputationalHodge.FullCircleRange
