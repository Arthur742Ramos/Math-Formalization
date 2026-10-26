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
theorem eigen_nonnegative (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient)
    (hn : u.val≠0) (he : laplacian ρ u=μ•u.val) : 0≤μ := by
  have h : 0≤pairing ρ (laplacian ρ u) u.val := quadratic_nonnegative ρ u
  rw [he,pairing_smul_left] at h
  have hp:=pairing_positive ρ u.val hn
  nlinarith

theorem normalized_kernel_zero (ρ : RegularDensity) (u : Domain ρ) (hz : laplacian ρ u.val=0) :
    u.val.val=0 := by
  obtain ⟨c,hc⟩:=(kernel_iff_constant ρ u.val).mp hz
  have hm : weightedMean ρ u.val.val=0 := u.property
  rw [hc,weightedMean_constant] at hm
  have h0 : c=0 := (mul_eq_zero.mp hm).resolve_right (ne_of_gt (mean_pos ρ.val))
  rw [hc,h0]
  rfl
theorem normalized_eigen_positive (ρ : RegularDensity) (μ : ℝ) (u : Domain ρ)
    (hn : u.val.val≠0) (he : laplacian ρ u.val=μ•u.val.val) : 0<μ := by
  have h:=eigen_nonnegative ρ μ u.val hn he
  have hz : μ≠0 := by
    intro hz
    subst μ
    exact hn (normalized_kernel_zero ρ u (by simpa only [zero_smul] using he))
  exact lt_of_le_of_ne h (Ne.symm hz)
theorem resonance_positive (ρ : RegularDensity) (μ : ℝ) (h : Resonant ρ μ) : 0<μ := by
  obtain ⟨u,hn,he⟩:=h
  change laplacian ρ u.val-μ•u.val.val=0 at he
  exact normalized_eigen_positive ρ μ u hn (sub_eq_zero.mp he)
theorem nonpositive_nonresonant (ρ : RegularDensity) (μ : ℝ) (hμ : μ≤0) : ¬Resonant ρ μ :=
  fun h => not_lt_of_ge hμ (resonance_positive ρ μ h)
theorem eigen_orthogonal (ρ : RegularDensity) (μ ν : ℝ) (u v : C2Coefficient)
    (hu : laplacian ρ u=μ•u.val) (hv : laplacian ρ v=ν•v.val) (hne : μ≠ν) :
    pairing ρ u.val v.val=0 := by
  have h:=laplacian_symmetric ρ u v
  rw [hu,hv,pairing_smul_left,pairing_smul_right] at h
  have hz : (μ-ν)*pairing ρ u.val v.val=0 := by nlinarith
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

/-- Necessary orthogonality for actual shifted solutions; all C2 competitors are covered. -/
theorem forcing_orthogonal (ρ : RegularDensity) (μ : ℝ) (u v : C2Coefficient) (f : Coefficient)
    (hv : laplacian ρ v=μ•v.val) (hu : laplacian ρ u-μ•u.val=f) : pairing ρ f v.val=0 := by
  rw [← hu,pairing_sub_left,laplacian_symmetric,hv,pairing_smul_right,pairing_smul_left,sub_self]
theorem domain_forcing_orthogonal (ρ : RegularDensity) (μ : ℝ) (u : Domain ρ)
    (v : C2Coefficient) (f : Coefficient) (hv : laplacian ρ v=μ•v.val)
    (hu : shifted ρ μ u=f) : pairing ρ f v.val=0 := forcing_orthogonal ρ μ u.val v f hv hu
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
theorem resonant_forcing_obstruction (ρ : RegularDensity) (μ : ℝ) (h : Resonant ρ μ) :
    ∃ f : Coefficient,f≠0 ∧
      (∀ p : Trace 0 0,lineIntegral (ρ.val.val*f) (fromTrace p)=0) ∧
      (∀ p : Trace 0 0,period p (meanHarmonic (ρ.val.val*f)).val=0) ∧
      ¬∃ u : C2Coefficient,laplacian ρ u-μ•u.val=f := by
  obtain ⟨v,hn,hv⟩:=h
  change laplacian ρ v.val-μ•v.val.val=0 at hv
  exact ⟨v.val.val,hn,(mode_periods ρ v).1,(mode_periods ρ v).2,
    mode_obstructed ρ μ v.val hn (sub_eq_zero.mp hv)⟩

/-- Explicit nonvacuous flat-circle resonance, with the existing geometer sign. -/
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
theorem cosine_mean_zero : weightedMean flatDensity cosine=0 := by
  have h:=weightedMean_laplacian flatDensity cosineC2
  rw [cosine_eigen,weightedMean_smul] at h
  exact (mul_eq_zero.mp h).resolve_left (ne_of_gt frequency_positive)
noncomputable def cosineMode : Domain flatDensity := ⟨cosineC2,cosine_mean_zero⟩
theorem cosine_nonzero : cosine≠0 := by
  intro h
  have he:=congrArg (fun f : Coefficient => f 0) h
  norm_num [cosine_zero] at he
theorem cosine_resonant : Resonant flatDensity frequency :=
  ⟨cosineMode,cosine_nonzero,sub_eq_zero.mpr cosine_eigen⟩
/-- Actual raw/cochain period compatibility does not suffice at the exhibited resonance. -/
theorem flat_counterexample : Resonant flatDensity frequency ∧
    (∀ p : Trace 0 0,lineIntegral (flatDensity.val.val*cosine) (fromTrace p)=0) ∧
    (∀ p : Trace 0 0,period p (meanHarmonic (flatDensity.val.val*cosine)).val=0) ∧
    ¬∃ u : C2Coefficient,laplacian flatDensity u-frequency•u.val=cosine :=
  ⟨cosine_resonant,(mode_periods flatDensity cosineMode).1,(mode_periods flatDensity cosineMode).2,
    mode_obstructed flatDensity frequency cosineC2 cosine_nonzero cosine_eigen⟩
end ComputationalHodge.ResonanceObstruction
