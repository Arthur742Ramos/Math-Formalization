module
public import FullOperator
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.LinearAlgebra.BilinearForm.Properties
@[expose] public section
namespace ComputationalHodge.CanonicalCircle
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson ComputationalHodge.GreenOperator ComputationalHodge.CompactGreen ComputationalHodge.CircleFredholm ComputationalHodge.ResonanceObstruction ComputationalHodge.FullCircleRange ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals MeasureTheory Set Function
open scoped Topology NNReal unitInterval ContDiff

/-- The actual unrestricted scalar circle Laplacian as an algebraic linear map. -/
noncomputable def laplaceMap (ρ : RegularDensity) : C2Coefficient →ₗ[ℝ] Coefficient where
  toFun := laplacian ρ
  map_add' := laplacian_add ρ
  map_smul' := laplacian_smul ρ
/-- The shifted differential expression on every actual C2 coefficient. -/
noncomputable def operator (ρ : RegularDensity) (μ : ℝ) : C2Coefficient →ₗ[ℝ] Coefficient :=
  laplaceMap ρ-μ•C2Space.subtype
/-- Actual homogeneous C2 solutions, with no external finite-dimensionality assumption. -/
noncomputable def homogeneousSpace (ρ : RegularDensity) (μ : ℝ) : Submodule ℝ C2Coefficient :=
  (operator ρ μ).ker
abbrev Homogeneous (ρ : RegularDensity) (μ : ℝ) := ↥(homogeneousSpace ρ μ)
noncomputable def reducedModes (ρ : RegularDensity) (μ : ℝ) : Submodule ℝ (Compatible ρ) :=
  (reduced ρ μ).ker
theorem reduced_fixed (ρ : RegularDensity) (μ : ℝ) (x : reducedModes ρ μ) :
    μ•greenMap ρ x.val=x.val :=
  (sub_eq_zero.mp (show x.val-μ•greenMap ρ x.val=0 from x.property)).symm
theorem reduced_modes_finite (ρ : RegularDensity) (μ : ℝ) :
    FiniteDimensional ℝ (reducedModes ρ μ) := by
  let A : Compatible ρ →ₗ[ℝ] Compatible ρ := (μ•greenMap ρ).toLinearMap
  have hpres : ∀ x∈reducedModes ρ μ,A x∈reducedModes ρ μ := by
    intro x hx
    have he : A x=x := reduced_fixed ρ μ ⟨x,hx⟩
    rw [he]
    exact hx
  have hc : IsCompactOperator A := (green_isCompactOperator ρ).smul μ
  have hr := hc.restrict hpres (ContinuousLinearMap.isClosed_ker (reduced ρ μ))
  have he : (A.restrict hpres : reducedModes ρ μ → reducedModes ρ μ)=id := by
    funext x
    apply Subtype.ext
    exact reduced_fixed ρ μ x
  exact FiniteDimensional.of_isCompactOperator_id (he ▸ hr)
theorem green_recovers (ρ : RegularDensity) (u : C2Coefficient) (hu : weightedMean ρ u.val=0) :
    solution ρ ⟨laplacian ρ u,weightedMean_laplacian ρ u⟩=u :=
  normalized_unique ρ _ u (solution_solves ρ _) (solution_mean_zero ρ _) hu
noncomputable def laplaceCompatible (ρ : RegularDensity) : C2Coefficient →ₗ[ℝ] Compatible ρ where
  toFun u := ⟨laplacian ρ u,weightedMean_laplacian ρ u⟩
  map_add' u v := Subtype.ext (laplacian_add ρ u v)
  map_smul' c u := Subtype.ext (laplacian_smul ρ c u)
noncomputable def kernelTransfer (ρ : RegularDensity) (μ : ℝ) (hμ : μ≠0) :
    Homogeneous ρ μ →ₗ[ℝ] reducedModes ρ μ where
  toFun u := ⟨laplaceCompatible ρ u.val,by
    apply Subtype.ext
    exact (congrArg (fun v : C2Coefficient => laplacian ρ u.val-μ•v.val)
      (green_recovers ρ u.val (nonzero_homogeneous_normalized ρ μ hμ u.val u.property))).trans u.property⟩
  map_add' u v := Subtype.ext (Subtype.ext (laplacian_add ρ u.val v.val))
  map_smul' c u := Subtype.ext (Subtype.ext (laplacian_smul ρ c u.val))
theorem kernelTransfer_injective (ρ : RegularDensity) (μ : ℝ) (hμ : μ≠0) :
    Injective (kernelTransfer ρ μ hμ) := fun u v h =>
  Subtype.ext (normalized_unique ρ u.val v.val
    (show laplacian ρ u.val=laplacian ρ v.val from congrArg (fun x : reducedModes ρ μ => x.val.val) h)
    (nonzero_homogeneous_normalized ρ μ hμ u.val u.property)
    (nonzero_homogeneous_normalized ρ μ hμ v.val v.property))
theorem homogeneous_finite (ρ : RegularDensity) (μ : ℝ) :
    FiniteDimensional ℝ (Homogeneous ρ μ) := by
  by_cases hμ : μ=0
  · subst μ
    let E : Homogeneous ρ 0 →ₗ[ℝ] ℝ :=
      { toFun := fun u => u.val.val 0
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine FiniteDimensional.of_injective (V₂ := ℝ) E ?_
    intro u v h
    have hu : fullShifted ρ 0 u.val=0 := u.property
    have hv : fullShifted ρ 0 v.val=0 := v.property
    obtain ⟨a,ha⟩ := (kernel_iff_constant ρ u.val).mp (by simpa only [fullShifted,zero_smul,sub_zero] using hu)
    obtain ⟨b,hb⟩ := (kernel_iff_constant ρ v.val).mp (by simpa only [fullShifted,zero_smul,sub_zero] using hv)
    have hab : a=b := by change u.val.val 0=v.val.val 0 at h;simpa only [ha,hb,constant,ContinuousMap.const_apply] using h
    exact Subtype.ext (Subtype.ext (ha.trans ((congrArg constant hab).trans hb.symm)))
  · have := reduced_modes_finite ρ μ
    exact FiniteDimensional.of_injective (V₂ := reducedModes ρ μ) (kernelTransfer ρ μ hμ) (kernelTransfer_injective ρ μ hμ)
theorem pairing_eq_weightedMean (ρ : RegularDensity) (f g : Coefficient) :
    pairing ρ f g=weightedMean ρ (f*g) := congrArg mean (mul_assoc ρ.val.val f g)
theorem pairing_add_left (ρ : RegularDensity) (f g h : Coefficient) :
    pairing ρ (f+g) h=pairing ρ f h+pairing ρ g h := by
  simp only [pairing_eq_weightedMean,add_mul,weightedMean_add]
theorem pairing_add_right (ρ : RegularDensity) (f g h : Coefficient) :
    pairing ρ f (g+h)=pairing ρ f g+pairing ρ f h := by
  rw [pairing_comm ρ f (g+h),pairing_add_left,pairing_comm ρ g f,pairing_comm ρ h f]
noncomputable def massForm (ρ : RegularDensity) : LinearMap.BilinForm ℝ C2Coefficient where
  toFun u :=
    { toFun := fun v => pairing ρ u.val v.val
      map_add' := fun v w => pairing_add_right ρ u.val v.val w.val
      map_smul' := fun c v => pairing_smul_right ρ c u.val v.val }
  map_add' u v := LinearMap.ext fun w => pairing_add_left ρ u.val v.val w.val
  map_smul' c u := LinearMap.ext fun v => pairing_smul_left ρ c u.val v.val
noncomputable def gram (ρ : RegularDensity) (μ : ℝ) : LinearMap.BilinForm ℝ (Homogeneous ρ μ) :=
  (massForm ρ).restrict (homogeneousSpace ρ μ)
theorem gram_nondegenerate (ρ : RegularDensity) (μ : ℝ) : (gram ρ μ).Nondegenerate := by
  have hz : ∀ u : Homogeneous ρ μ,gram ρ μ u u=0 → u=0 := fun u h =>
    Classical.byContradiction fun hn =>
      (ne_of_gt (pairing_positive ρ u.val.val (fun he => hn (Subtype.ext (Subtype.ext he))))) h
  exact ⟨fun u hu => hz u (hu u),fun u hu => hz u (hu u)⟩
noncomputable def kernelFunctional (ρ : RegularDensity) (μ : ℝ) :
    C2Coefficient →ₗ[ℝ] Module.Dual ℝ (Homogeneous ρ μ) where
  toFun u := (massForm ρ u).comp (homogeneousSpace ρ μ).subtype
  map_add' u v := LinearMap.ext fun k => pairing_add_left ρ u.val v.val k.val.val
  map_smul' c u := LinearMap.ext fun k => pairing_smul_left ρ c u.val k.val.val
noncomputable def gramEquiv (ρ : RegularDensity) (μ : ℝ) :
    Homogeneous ρ μ ≃ₗ[ℝ] Module.Dual ℝ (Homogeneous ρ μ) := by
  letI := homogeneous_finite ρ μ
  exact LinearMap.BilinForm.toDual (K := ℝ) (V := Homogeneous ρ μ) (gram ρ μ) (gram_nondegenerate ρ μ)
/-- Finite Gram projection into the actual homogeneous C2 kernel. -/
noncomputable def kernelProjector (ρ : RegularDensity) (μ : ℝ) : C2Coefficient →ₗ[ℝ] C2Coefficient :=
  (homogeneousSpace ρ μ).subtype.comp ((gramEquiv ρ μ).symm.toLinearMap.comp (kernelFunctional ρ μ))
theorem projector_mem (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) :
    kernelProjector ρ μ u∈homogeneousSpace ρ μ := ((gramEquiv ρ μ).symm (kernelFunctional ρ μ u)).property
theorem projector_pairing (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) (k : Homogeneous ρ μ) :
    pairing ρ (kernelProjector ρ μ u).val k.val.val=pairing ρ u.val k.val.val :=
  congrArg (fun f : Module.Dual ℝ (Homogeneous ρ μ) => f k)
    ((gramEquiv ρ μ).apply_symm_apply (kernelFunctional ρ μ u))
noncomputable def canonicalizer (ρ : RegularDensity) (μ : ℝ) : C2Coefficient →ₗ[ℝ] C2Coefficient :=
  LinearMap.id-kernelProjector ρ μ
def OrthogonalToKernel (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) : Prop :=
  ∀ v : C2Coefficient,fullShifted ρ μ v=0 → pairing ρ u.val v.val=0
theorem canonicalizer_preserves (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) :
    fullShifted ρ μ (canonicalizer ρ μ u)=fullShifted ρ μ u := by
  change operator ρ μ (u-kernelProjector ρ μ u)=operator ρ μ u
  rw [map_sub,show operator ρ μ (kernelProjector ρ μ u)=0 from projector_mem ρ μ u,sub_zero]
theorem canonicalizer_orthogonal (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) :
    OrthogonalToKernel ρ μ (canonicalizer ρ μ u) := fun v hv =>
  (pairing_sub_left ρ u.val (kernelProjector ρ μ u).val v.val).trans
    (sub_eq_zero.mpr (projector_pairing ρ μ u ⟨v,hv⟩).symm)
theorem orthogonal_unique (ρ : RegularDensity) (μ : ℝ) (u v : C2Coefficient)
    (h : fullShifted ρ μ u=fullShifted ρ μ v)
    (hu : OrthogonalToKernel ρ μ u) (hv : OrthogonalToKernel ρ μ v) : u=v := by
  have hd : fullShifted ρ μ (u-v)=0 := (fullShifted_sub ρ μ u v).trans (sub_eq_zero.mpr h)
  have hz : pairing ρ (u-v).val (u-v).val=0 := by
    change pairing ρ (u.val-v.val) (u-v).val=0
    rw [pairing_sub_left,hu (u-v) hd,hv (u-v) hd,sub_self]
  by_contra hn
  have hne : (u-v).val≠0 := fun he => hn (sub_eq_zero.mp (Subtype.ext he))
  exact (ne_of_gt (pairing_positive ρ (u-v).val hne)) hz
theorem canonicalizer_independent (ρ : RegularDensity) (μ : ℝ) (u v : C2Coefficient)
    (h : fullShifted ρ μ u=fullShifted ρ μ v) : canonicalizer ρ μ u=canonicalizer ρ μ v :=
  orthogonal_unique ρ μ _ _ ((canonicalizer_preserves ρ μ u).trans (h.trans (canonicalizer_preserves ρ μ v).symm))
    (canonicalizer_orthogonal ρ μ u) (canonicalizer_orthogonal ρ μ v)
/-- Every solvable actual equation has one kernel-orthogonal actual C2 representative. -/
theorem solvable_iff_unique_orthogonal (ρ : RegularDensity) (μ : ℝ) (f : Coefficient) :
    (∃ u : C2Coefficient,fullShifted ρ μ u=f) ↔
      ∃! u : C2Coefficient,fullShifted ρ μ u=f ∧ OrthogonalToKernel ρ μ u :=
  ⟨fun ⟨u,hu⟩ => ⟨canonicalizer ρ μ u,⟨(canonicalizer_preserves ρ μ u).trans hu,canonicalizer_orthogonal ρ μ u⟩,
    fun v hv => orthogonal_unique ρ μ v (canonicalizer ρ μ u) (hv.1.trans ((canonicalizer_preserves ρ μ u).trans hu).symm) hv.2 (canonicalizer_orthogonal ρ μ u)⟩,
   fun ⟨u,hu,_⟩ => ⟨u,hu.1⟩⟩
/-- Weighted L2 mass: the integral of rho times the squared actual function. -/
noncomputable def mass (ρ : RegularDensity) (u : C2Coefficient) : ℝ := pairing ρ u.val u.val
theorem mass_zero (ρ : RegularDensity) : mass ρ 0=0 := by
  simpa only [mass,Submodule.coe_zero,sub_self] using pairing_sub_left ρ 0 0 0
theorem mass_nonneg (ρ : RegularDensity) (u : C2Coefficient) : 0≤mass ρ u :=
  (eq_or_ne u 0).elim (fun hu => le_of_eq ((congrArg (mass ρ) hu).trans (mass_zero ρ)).symm)
    (fun hu => (pairing_positive ρ u.val (fun he => hu (Subtype.ext he))).le)
theorem mass_eq_zero_iff (ρ : RegularDensity) (u : C2Coefficient) : mass ρ u=0 ↔ u=0 :=
  ⟨fun h => Classical.byContradiction fun hu =>
    (ne_of_gt (pairing_positive ρ u.val (fun he => hu (Subtype.ext he)))) h,
   fun hu => hu ▸ mass_zero ρ⟩
theorem canonicalizer_idempotent (ρ : RegularDensity) (μ : ℝ) (u : C2Coefficient) :
    canonicalizer ρ μ (canonicalizer ρ μ u)=canonicalizer ρ μ u :=
  orthogonal_unique ρ μ _ _ (canonicalizer_preserves ρ μ (canonicalizer ρ μ u))
    (canonicalizer_orthogonal ρ μ (canonicalizer ρ μ u)) (canonicalizer_orthogonal ρ μ u)
/-- Pythagoras for weighted L2 mass along the actual solution coset. -/
theorem mass_pythagorean (ρ : RegularDensity) (μ : ℝ) (u w : C2Coefficient)
    (h : fullShifted ρ μ w=fullShifted ρ μ u) :
    mass ρ w=mass ρ (canonicalizer ρ μ u)+mass ρ (w-canonicalizer ρ μ u) := by
  let c:=canonicalizer ρ μ u
  have hd : fullShifted ρ μ (w-c)=0 :=
    (fullShifted_sub ρ μ w c).trans (sub_eq_zero.mpr (h.trans (canonicalizer_preserves ρ μ u).symm))
  have hc : pairing ρ c.val (w-c).val=0 := canonicalizer_orthogonal ρ μ u (w-c) hd
  have hw : w=c+(w-c) := by abel
  conv_lhs => rw [hw]
  change pairing ρ (c.val+(w-c).val) (c.val+(w-c).val)=pairing ρ c.val c.val+pairing ρ (w-c).val (w-c).val
  rw [pairing_add_left,pairing_add_right,pairing_add_right,hc,pairing_comm ρ (w-c).val c.val,hc]
  ring
theorem mass_minimum (ρ : RegularDensity) (μ : ℝ) (u w : C2Coefficient)
    (h : fullShifted ρ μ w=fullShifted ρ μ u) : mass ρ (canonicalizer ρ μ u)≤mass ρ w :=
  (le_add_of_nonneg_right (mass_nonneg ρ (w-canonicalizer ρ μ u))).trans (mass_pythagorean ρ μ u w h).symm.le
theorem mass_minimum_equality (ρ : RegularDensity) (μ : ℝ) (u w : C2Coefficient)
    (h : fullShifted ρ μ w=fullShifted ρ μ u) :
    mass ρ w=mass ρ (canonicalizer ρ μ u) ↔ w=canonicalizer ρ μ u := by
  rw [mass_pythagorean ρ μ u w h,add_eq_left,mass_eq_zero_iff,sub_eq_zero]
theorem zero_orthogonal_iff_mean (ρ : RegularDensity) (u : C2Coefficient) :
    OrthogonalToKernel ρ 0 u ↔ weightedMean ρ u.val=0 := by
  constructor
  · intro hu
    have hc : fullShifted ρ 0 (constantC2 1)=0 := by rw [fullShifted_constant];ext q;simp [constant]
    simpa only [Poisson.constantC2,pairing_one_right] using hu (constantC2 1) hc
  · intro hu v hv
    obtain ⟨c,hc⟩ := (kernel_iff_constant ρ v).mp (by simpa only [fullShifted,zero_smul,sub_zero] using hv)
    rw [hc,pairing_comm,pairing_constant_left,hu,mul_zero]
theorem canonicalizer_zero_eq_normalize (ρ : RegularDensity) (u : C2Coefficient) :
    canonicalizer ρ 0 u=normalize ρ u := by
  have hn : fullShifted ρ 0 (normalize ρ u)=fullShifted ρ 0 u := by
    simpa only [fullShifted,zero_smul,sub_zero] using normalize_laplacian ρ u
  exact orthogonal_unique ρ 0 _ _ ((canonicalizer_preserves ρ 0 u).trans hn.symm)
    (canonicalizer_orthogonal ρ 0 u) ((zero_orthogonal_iff_mean ρ _).mpr (normalize_mean_zero ρ u))
/-- Literal computational-trace compatibility is equivalent to one canonical actual C2 solution. -/
theorem zero_raw_iff_unique (ρ : RegularDensity) (f : Coefficient) :
    (∀ p : Trace 0 0,lineIntegral (ρ.val.val*f) (fromTrace p)=0) ↔
      ∃! u : C2Coefficient,fullShifted ρ 0 u=f ∧ OrthogonalToKernel ρ 0 u :=
  (zero_solvable_iff_raw ρ f).symm.trans (solvable_iff_unique_orthogonal ρ 0 f)
theorem zero_cochain_iff_unique (ρ : RegularDensity) (f : Coefficient) :
    (∀ p : Trace 0 0,period p (meanHarmonic (ρ.val.val*f)).val=0) ↔
      ∃! u : C2Coefficient,fullShifted ρ 0 u=f ∧ OrthogonalToKernel ρ 0 u := by
  simpa only [lineIntegral_fromTrace_harmonic] using zero_raw_iff_unique ρ f
theorem canonicalizer_zero_green (ρ : RegularDensity) (f : Coefficient) (u : C2Coefficient)
    (hu : fullShifted ρ 0 u=f) : canonicalizer ρ 0 u=green ρ f := by
  have hm : weightedMean ρ f=0 := by rw [← hu,weightedMean_fullShifted,neg_zero,zero_mul]
  have hg : fullShifted ρ 0 (green ρ f)=f := by
    simpa only [fullShifted,zero_smul,sub_zero,project_eq_self ρ f hm] using green_solves_projected ρ f
  exact orthogonal_unique ρ 0 _ _ ((canonicalizer_preserves ρ 0 u).trans (hu.trans hg.symm))
    (canonicalizer_orthogonal ρ 0 u) ((zero_orthogonal_iff_mean ρ _).mpr (green_mean_zero ρ f))
end ComputationalHodge.CanonicalCircle
