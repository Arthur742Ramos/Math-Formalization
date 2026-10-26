module
public import Positive
@[expose] public section
namespace ComputationalHodge.ResolventLimit
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson ComputationalHodge.GreenOperator ComputationalHodge.PositiveResolvent ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals ComputationalHodge.LoopCharacters Filter Set
open scoped Topology

/-- The scalar constant zero-mode, not an analytic one-form or a finite cochain. -/
noncomputable def harmonicPart (ρ : RegularDensity) (f : Coefficient) : Coefficient :=
  constant (weightedMean ρ f/mean ρ.val.val)
theorem harmonicPart_add (ρ : RegularDensity) (f g : Coefficient) :
    harmonicPart ρ (f+g)=harmonicPart ρ f+harmonicPart ρ g :=
  ContinuousMap.ext fun _ => (congrArg (fun x : ℝ => x/mean ρ.val.val) (weightedMean_add ρ f g)).trans (add_div _ _ _)
theorem harmonicPart_smul (ρ : RegularDensity) (c : ℝ) (f : Coefficient) :
    harmonicPart ρ (c•f)=c•harmonicPart ρ f :=
  ContinuousMap.ext fun _ => (congrArg (fun x : ℝ => x/mean ρ.val.val) (weightedMean_smul ρ c f)).trans (mul_div_assoc _ _ _)
theorem harmonicPart_idempotent (ρ : RegularDensity) (f : Coefficient) :
    harmonicPart ρ (harmonicPart ρ f)=harmonicPart ρ f := by simp only [harmonicPart,weightedMean_constant,mul_div_cancel_right₀ _ (ne_of_gt (mean_pos ρ.val))]
theorem harmonicPart_zero_iff (ρ : RegularDensity) (f : Coefficient) :
    harmonicPart ρ f=0 ↔ weightedMean ρ f=0 :=
  ⟨fun h => (div_eq_zero_iff.mp (congrArg (fun z : Coefficient => z 0) h)).resolve_right (ne_of_gt (mean_pos ρ.val)),
    fun h => by ext q; simp [harmonicPart,h,constant]⟩
theorem harmonicPart_kernel (ρ : RegularDensity) (f : Coefficient) :
    laplacian ρ (constantC2 (weightedMean ρ f/mean ρ.val.val))=0 :=
  laplacian_of_constant ρ _ _ rfl
theorem harmonicPart_fixes_kernel (ρ : RegularDensity) (u : C2Coefficient)
    (hu : laplacian ρ u=0) : harmonicPart ρ u.val=u.val := by
  obtain ⟨c,hc⟩ := (kernel_iff_constant ρ u).mp hu
  rw [hc,harmonicPart,weightedMean_constant,mul_div_cancel_right₀ _ (ne_of_gt (mean_pos ρ.val))]

/-- The explicit bound for the already constructed compatible Green map. -/
noncomputable def greenConstant (ρ : RegularDensity) : ℝ := 4*(mean ρ.val.val)^2
theorem greenConstant_pos (ρ : RegularDensity) : 0<greenConstant ρ :=
  mul_pos (by norm_num) (sq_pos_of_pos (mean_pos ρ.val))
theorem solve_mean_zero (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ)
    (f : Coefficient) (hf : weightedMean ρ f=0) : weightedMean ρ (solve ρ κ hκ f).val=0 :=
  (resolvent_weightedMean ρ κ hκ f).trans (by rw [hf,zero_div])
theorem solve_laplacian (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) :
    laplacian ρ (solve ρ κ hκ f)=f-κ•(solve ρ κ hκ f).val :=
  eq_sub_of_add_eq (solve_equation ρ κ hκ f)
theorem green_recovers (ρ : RegularDensity) (u : C2Coefficient) (hu : weightedMean ρ u.val=0) :
    green ρ (laplacian ρ u)=u :=
  normalized_unique ρ _ _ ((green_solves_projected ρ _).trans (project_eq_self ρ _ (weightedMean_laplacian ρ u))) (green_mean_zero ρ _) hu
/-- Actual C2 normalization identifies the resolvent with a constructed Green solution. -/
theorem normalized_identity (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ)
    (f : Coefficient) (hf : weightedMean ρ f=0) :
    solve ρ κ hκ f=green ρ (f-κ•resolvent ρ κ hκ f) := by
  simpa only [solve_laplacian,resolvent_apply] using (green_recovers ρ (solve ρ κ hκ f) (solve_mean_zero ρ κ hκ f hf)).symm
/-- Absorption gives a uniform compatible-sector estimate for small positive parameters. -/
theorem compatible_bound (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ)
    (hs : κ*greenConstant ρ≤1/2) (f : Coefficient) (hf : weightedMean ρ f=0) :
    ‖resolvent ρ κ hκ f‖≤2*greenConstant ρ*‖f‖ := by
  have hM := (greenConstant_pos ρ).le
  have hz : weightedMean ρ (f-κ•resolvent ρ κ hκ f)=0 := by
    rw [weightedMean_sub,weightedMean_smul,resolvent_weightedMean,hf,zero_div,mul_zero,sub_self]
  have hb := green_bound ρ _ hz
  rw [← normalized_identity ρ κ hκ f hf] at hb
  change ‖resolvent ρ κ hκ f‖≤greenConstant ρ*‖f-κ•resolvent ρ κ hκ f‖ at hb
  have ht := norm_sub_le f (κ•resolvent ρ κ hκ f)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hκ] at ht
  have hp := mul_le_mul_of_nonneg_left ht hM
  have ha := mul_le_mul_of_nonneg_right hs (norm_nonneg (resolvent ρ κ hκ f))
  nlinarith
/-- The actual finite part has a quantitative C0 error tending to zero. -/
theorem compatible_error (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ)
    (hs : κ*greenConstant ρ≤1/2) (f : Coefficient) (hf : weightedMean ρ f=0) :
    ‖resolvent ρ κ hκ f-(green ρ f).val‖≤2*κ*(greenConstant ρ)^2*‖f‖ := by
  let g : Compatible ρ := ⟨f,hf⟩
  let r : Compatible ρ := ⟨resolvent ρ κ hκ f,solve_mean_zero ρ κ hκ f hf⟩
  have he : resolvent ρ κ hκ f=(greenMap ρ (g-κ•r)).val := congrArg (fun u : C2Coefficient => u.val) (normalized_identity ρ κ hκ f hf)
  change ‖resolvent ρ κ hκ f-(greenMap ρ g).val‖≤_
  rw [he]
  simp only [map_sub,map_smul,Submodule.coe_sub,Submodule.coe_smul,sub_sub_cancel_left,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hκ]
  have hg : ‖(greenMap ρ r).val‖≤greenConstant ρ*‖resolvent ρ κ hκ f‖ := greenMap_bound ρ r
  nlinarith [mul_le_mul_of_nonneg_left hg hκ.le,
    mul_le_mul_of_nonneg_left (compatible_bound ρ κ hκ hs f hf) (mul_nonneg hκ.le (greenConstant_pos ρ).le)]

/-- Remove the true constant zero-mode singularity from the entire-forcing resolvent. -/
noncomputable def finitePart (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) : Coefficient :=
  resolvent ρ κ hκ f-κ⁻¹•harmonicPart ρ f
theorem finitePart_eq_projected (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) :
    finitePart ρ κ hκ f=resolvent ρ κ hκ (projectForcing ρ f) := by
  rw [projectForcing,map_sub,resolvent_constant]
  ext q
  change resolvent ρ κ hκ f q-κ⁻¹*(weightedMean ρ f/mean ρ.val.val)=
    resolvent ρ κ hκ f q-(weightedMean ρ f/mean ρ.val.val)/κ
  ring
theorem green_projected (ρ : RegularDensity) (f : Coefficient) :
    green ρ (projectForcing ρ f)=green ρ f :=
  congrArg (fun g : Coefficient => normalize ρ (baseSolution ρ g)) (project_eq_self ρ _ (project_mean_zero ρ f))
theorem finitePart_error (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ)
    (hs : κ*greenConstant ρ≤1/2) (f : Coefficient) :
    ‖finitePart ρ κ hκ f-(green ρ f).val‖≤2*κ*(greenConstant ρ)^2*‖projectForcing ρ f‖ := by
  simpa only [finitePart_eq_projected,green_projected] using compatible_error ρ κ hκ hs (projectForcing ρ f) (project_mean_zero ρ f)
theorem scaled_decomposition (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ) (f : Coefficient) :
    κ•resolvent ρ κ hκ f=harmonicPart ρ f+κ•finitePart ρ κ hκ f := by
  rw [finitePart,smul_sub,smul_smul,mul_inv_cancel₀ hκ.ne',one_smul]
  module
theorem residue_error (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ)
    (hs : κ*greenConstant ρ≤1/2) (f : Coefficient) :
    ‖κ•resolvent ρ κ hκ f-harmonicPart ρ f‖≤2*κ*greenConstant ρ*‖projectForcing ρ f‖ := by
  rw [scaled_decomposition,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hκ,finitePart_eq_projected]
  exact (mul_le_mul_of_nonneg_left (compatible_bound ρ κ hκ hs _ (project_mean_zero ρ f)) hκ.le).trans_eq (by ring)

/-- Every positive parameter family tending to zero recovers the actual Green finite part in C0. -/
theorem finitePart_tendsto {α : Type*} {l : Filter α} (ρ : RegularDensity)
    (κ : α→ℝ) (hκ : ∀ a,0<κ a) (hlim : Tendsto κ l (𝓝 0)) (f : Coefficient) :
    Tendsto (fun a => finitePart ρ (κ a) (hκ a) f) l (𝓝 (green ρ f).val) := by
  have hs : ∀ᶠ a in l,κ a*greenConstant ρ≤1/2 :=
    ((hlim.mul_const (greenConstant ρ)).eventually (gt_mem_nhds (by norm_num))).mono (fun _ h => h.le)
  have hb : Tendsto (fun a => 2*κ a*(greenConstant ρ)^2*‖projectForcing ρ f‖) l (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using (((tendsto_const_nhds.mul hlim).mul_const ((greenConstant ρ)^2)).mul_const ‖projectForcing ρ f‖)
  exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm' (hs.mono (fun a ha => finitePart_error ρ (κ a) (hκ a) ha f)) hb)
/-- The scaled genuine resolvent converges in C0 to the scalar harmonic projection. -/
theorem residue_tendsto {α : Type*} {l : Filter α} (ρ : RegularDensity)
    (κ : α→ℝ) (hκ : ∀ a,0<κ a) (hlim : Tendsto κ l (𝓝 0)) (f : Coefficient) :
    Tendsto (fun a => κ a•resolvent ρ (κ a) (hκ a) f) l (𝓝 (harmonicPart ρ f)) := by
  simpa only [zero_smul,add_zero,← scaled_decomposition] using
    ((tendsto_const_nhds : Tendsto (fun _ : α => harmonicPart ρ f) l (𝓝 (harmonicPart ρ f))).add (hlim.smul (finitePart_tendsto ρ κ hκ hlim f)))

/-- Vanishing of the scalar residue is exactly the actual weighted based-loop obstruction. -/
theorem harmonicPart_zero_iff_raw (ρ : RegularDensity) (f : Coefficient) :
    harmonicPart ρ f=0 ↔ ∀ p : Trace 0 0,lineIntegral (ρ.val.val*f) (fromTrace p)=0 :=
  (harmonicPart_zero_iff ρ f).trans (compatible_iff_raw ρ f)
theorem harmonicPart_zero_iff_cochain (ρ : RegularDensity) (f : Coefficient) :
    harmonicPart ρ f=0 ↔ ∀ p : Trace 0 0,period p (meanHarmonic (ρ.val.val*f)).val=0 := by
  simpa only [lineIntegral_fromTrace_harmonic] using harmonicPart_zero_iff_raw ρ f
/-- Every actual based-loop period is preserved by the scaled resolvent, for every positive parameter. -/
theorem scaled_resolvent_raw_period (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ)
    (f : Coefficient) (p : Trace 0 0) :
    lineIntegral (ρ.val.val*(κ•resolvent ρ κ hκ f)) (fromTrace p)=lineIntegral (ρ.val.val*f) (fromTrace p) := by
  rw [lineIntegral_eq_mean,lineIntegral_eq_mean]
  change weightedMean ρ (κ•resolvent ρ κ hκ f)*_=weightedMean ρ f*_
  rw [weightedMean_smul,resolvent_weightedMean,mul_div_cancel₀ _ hκ.ne']
theorem scaled_resolvent_cochain_period (ρ : RegularDensity) (κ : ℝ) (hκ : 0<κ)
    (f : Coefficient) (p : Trace 0 0) :
    period p (meanHarmonic (ρ.val.val*(κ•resolvent ρ κ hκ f))).val=period p (meanHarmonic (ρ.val.val*f)).val := by
  simpa only [lineIntegral_fromTrace_harmonic] using scaled_resolvent_raw_period ρ κ hκ f p
end ComputationalHodge.ResolventLimit
