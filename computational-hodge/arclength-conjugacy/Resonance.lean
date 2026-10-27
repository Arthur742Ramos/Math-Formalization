module
public import Fredholm
@[expose] public section
namespace ComputationalHodge.ResonanceObstruction
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson
open ComputationalHodge.GreenOperator ComputationalHodge.CircleFredholm
open ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals ComputationalHodge.LoopCharacters
open MeasureTheory Set
open scoped Topology NNReal unitInterval ContDiff

theorem pairing_comm (ρ : RegularDensity) (f g : Coefficient) : pairing ρ f g=pairing ρ g f := by
  unfold pairing
  congr 1
  ext q
  change ρ.val.val q*f q*g q=ρ.val.val q*g q*f q
  ring
theorem pairing_sub_left (ρ : RegularDensity) (f g h : Coefficient) :
    pairing ρ (f-g) h=pairing ρ f h-pairing ρ g h := by
  have he : ρ.val.val*(f-g)*h=ρ.val.val*f*h-ρ.val.val*g*h := by
    ext q
    change ρ.val.val q*(f q-g q)*h q=ρ.val.val q*f q*h q-ρ.val.val q*g q*h q
    ring
  rw [pairing,he,mean_sub]
  rfl
theorem pairing_smul_left (ρ : RegularDensity) (c : ℝ) (f g : Coefficient) :
    pairing ρ (c•f) g=c*pairing ρ f g := by
  have he : ρ.val.val*(c•f)*g=c•(ρ.val.val*f*g) := by
    ext q
    change ρ.val.val q*(c*f q)*g q=c*(ρ.val.val q*f q*g q)
    ring
  rw [pairing,he,mean_smul]
  rfl
theorem pairing_smul_right (ρ : RegularDensity) (c : ℝ) (f g : Coefficient) :
    pairing ρ f (c•g)=c*pairing ρ f g := by
  rw [pairing_comm,pairing_smul_left,pairing_comm ρ g f]
theorem pairing_positive (ρ : RegularDensity) (f : Coefficient) (hf : f≠0) : 0<pairing ρ f f := by
  obtain ⟨q,hq⟩ : ∃ q,f q≠0 := by
    by_contra h
    apply hf
    ext q
    exact not_ne_iff.mp (not_exists.mp h q)
  rw [pairing,mean_circle]
  apply integral_pos_of_integrable_nonneg_nonzero (ρ.val.val*f*f).continuous
    (continuous_integrable (ρ.val.val*f*f).continuous)
    (fun q => by
      change 0≤ρ.val.val q*f q*f q
      simpa only [mul_assoc] using mul_nonneg (ρ.val.property q).le (mul_self_nonneg (f q)))
  change ρ.val.val q*f q*f q≠0
  exact mul_ne_zero (mul_ne_zero (density_ne ρ.val q) hq) hq

theorem laplacian_symmetric (ρ : RegularDensity) (u v : C2Coefficient) :
    pairing ρ (laplacian ρ u) v.val=pairing ρ u.val (laplacian ρ v) :=
  pairing_symmetry ρ u v
/-- Necessary orthogonality for actual shifted solutions; all C2 competitors are covered. -/
theorem forcing_orthogonal (ρ : RegularDensity) (μ : ℝ) (u v : C2Coefficient) (f : Coefficient)
    (hv : laplacian ρ v=μ•v.val) (hu : laplacian ρ u-μ•u.val=f) : pairing ρ f v.val=0 := by
  rw [← hu,pairing_sub_left,laplacian_symmetric,hv,pairing_smul_right,pairing_smul_left,sub_self]
theorem mode_obstructed (ρ : RegularDensity) (μ : ℝ) (v : C2Coefficient)
    (hn : v.val≠0) (hv : laplacian ρ v=μ•v.val) :
    ¬∃ u : C2Coefficient,laplacian ρ u-μ•u.val=v.val := by
  rintro ⟨u,hu⟩
  exact (ne_of_gt (pairing_positive ρ v.val hn)) (forcing_orthogonal ρ μ u v v.val hv hu)
theorem mode_periods (ρ : RegularDensity) (v : Domain ρ) :
    (∀ p : Trace 0 0,lineIntegral (ρ.val.val*v.val.val) (fromTrace p)=0) ∧
    (∀ p : Trace 0 0,period p (meanHarmonic (ρ.val.val*v.val.val)).val=0) := by
  have h (p : Trace 0 0) : lineIntegral (ρ.val.val*v.val.val) (fromTrace p)=0 := by
    rw [lineIntegral_eq_mean,show mean (ρ.val.val*v.val.val)=0 from v.property,zero_mul]
  exact ⟨h,fun p => (lineIntegral_fromTrace_harmonic _ p).symm.trans (h p)⟩
/-- The constant unit density on the scalar circle. -/
noncomputable def flatDensity : RegularDensity :=
  ⟨⟨constant 1,fun _ => by change 0<(1 : ℝ);norm_num⟩,by
    change ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ))
    exact contDiff_const⟩

noncomputable def frequency : ℝ := (2*Real.pi)^2
theorem frequency_positive : 0<frequency := by unfold frequency;positivity
theorem cosine_eigen : laplacian flatDensity cosineC2=frequency•cosine := by
  have h1 (x : ℝ) : HasDerivAt (cover cosine) (-(2*Real.pi)*Real.sin (2*Real.pi*x)) x := by
    rw [show cover cosine=(fun t => Real.cos (2*Real.pi*t)) from funext cosine_cover]
    have h:=(((hasDerivAt_id x).const_mul (2*Real.pi)).cos)
    simp only [id_eq,mul_one] at h
    convert h using 1; ring
  have h2 (x : ℝ) : HasDerivAt (fun t => -(2*Real.pi)*Real.sin (2*Real.pi*t))
      (-frequency*Real.cos (2*Real.pi*x)) x := by
    have h:=((((hasDerivAt_id x).const_mul (2*Real.pi)).sin).const_mul (-(2*Real.pi)))
    simp only [id_eq,mul_one] at h
    convert h using 1; dsimp only [frequency]; ring
  have hd : deriv (cover cosine)=(fun t => -(2*Real.pi)*Real.sin (2*Real.pi*t)) :=
    funext (fun x => (h1 x).deriv)
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change cover (laplacian flatDensity cosineC2) x=frequency*cover cosine x
  rw [laplacian_cover]
  change -(deriv (fun t => deriv (cover cosine) t/(1 : ℝ)) x)/1=frequency*cover cosine x
  simp only [div_one]
  rw [hd,(h2 x).deriv,cosine_cover]
  ring
end ComputationalHodge.ResonanceObstruction
