module
public import Resonance
public import Mathlib.Analysis.Normed.Operator.Mul
@[expose] public section
namespace ComputationalHodge.ResonantRange
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson ComputationalHodge.GreenOperator ComputationalHodge.CompactGreen ComputationalHodge.CircleFredholm ComputationalHodge.ResonanceObstruction ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals MeasureTheory Set Function Topology Module

/-- Continuous literal weighted integral, in the original C0 norm. -/
noncomputable def modeFunctional (ρ : RegularDensity) (k : Compatible ρ) : Compatible ρ →L[ℝ] ℝ :=
  ((meanFunctional ρ).comp ((ContinuousLinearMap.mul ℝ Coefficient).flip k.val)).comp
    (compatibleSpace ρ).subtypeL
theorem modeFunctional_apply (ρ : RegularDensity) (k f : Compatible ρ) :
    modeFunctional ρ k f=pairing ρ f.val k.val :=
  congrArg mean (mul_assoc ρ.val.val f.val k.val).symm
/-- Orthogonality to the actual reduced kernel, with no Hilbert-space identification. -/
noncomputable def orthogonalSpace (ρ : RegularDensity) (μ : ℝ) : Submodule ℝ (Compatible ρ) :=
  ⨅ k : (reduced ρ μ).ker,(modeFunctional ρ k.val).ker
theorem orthogonal_mem (ρ : RegularDensity) (μ : ℝ) (f : Compatible ρ) :
    f∈orthogonalSpace ρ μ ↔ ∀ k : Compatible ρ,reduced ρ μ k=0 → pairing ρ f.val k.val=0 := by
  rw [orthogonalSpace,Submodule.mem_iInf]
  change (∀ k : (reduced ρ μ).ker,modeFunctional ρ k.val f=0) ↔ _
  simp only [modeFunctional_apply]
  exact ⟨fun h k hk => h ⟨k,hk⟩,fun h k => h k.val k.property⟩
theorem orthogonal_closed (ρ : RegularDensity) (μ : ℝ) :
    IsClosed (orthogonalSpace ρ μ : Set (Compatible ρ)) := by
  simpa only [orthogonalSpace,Submodule.coe_iInf] using
    isClosed_iInter (fun k : (reduced ρ μ).ker => (modeFunctional ρ k.val).isClosed_ker)
instance orthogonal_complete (ρ : RegularDensity) (μ : ℝ) : CompleteSpace (orthogonalSpace ρ μ) :=
  (orthogonal_closed ρ μ).completeSpace_coe
theorem scaled_green_symmetric (ρ : RegularDensity) (μ : ℝ) (x k : Compatible ρ) :
    pairing ρ (μ•greenMap ρ x).val k.val=pairing ρ x.val (μ•greenMap ρ k).val := by
  change pairing ρ (μ•(greenMap ρ x).val) k.val=pairing ρ x.val (μ•(greenMap ρ k).val)
  rw [pairing_smul_left,pairing_smul_right,pairing_comm ρ (greenMap ρ x).val k.val,
    ← greenMap_pairing_symmetry ρ x k]
theorem orthogonal_invariant (ρ : RegularDensity) (μ : ℝ) (x : Compatible ρ)
    (hx : x∈orthogonalSpace ρ μ) : μ•greenMap ρ x∈orthogonalSpace ρ μ := by
  apply (orthogonal_mem ρ μ _).mpr
  intro k hk
  have he : μ•greenMap ρ k=k := by
    change k-μ•greenMap ρ k=0 at hk
    exact (sub_eq_zero.mp hk).symm
  rw [scaled_green_symmetric,he]
  exact (orthogonal_mem ρ μ x).mp hx k hk
noncomputable def restrictedOperator (ρ : RegularDensity) (μ : ℝ) :
    orthogonalSpace ρ μ →L[ℝ] orthogonalSpace ρ μ :=
  (μ•greenMap ρ).restrict (orthogonal_invariant ρ μ)
noncomputable def restrictedReduced (ρ : RegularDensity) (μ : ℝ) :
    orthogonalSpace ρ μ →L[ℝ] orthogonalSpace ρ μ :=
  (reduced ρ μ).restrict (fun x hx =>
    (orthogonalSpace ρ μ).sub_mem hx (orthogonal_invariant ρ μ x hx))
theorem restricted_compact (ρ : RegularDensity) (μ : ℝ) :
    IsCompactOperator (restrictedOperator ρ μ) :=
  ((green_isCompactOperator ρ).smul μ).restrict (orthogonal_invariant ρ μ) (orthogonal_closed ρ μ)
theorem restricted_not_eigen (ρ : RegularDensity) (μ : ℝ) :
    ¬Module.End.HasEigenvalue (R := ℝ) (M := ↥(orthogonalSpace ρ μ))
      (restrictedOperator ρ μ).toLinearMap (1 : ℝ) := by
  intro h
  obtain ⟨x,hx⟩:=h.exists_hasEigenvector
  have he : restrictedOperator ρ μ x=x := by simpa using hx.apply_eq_smul
  have hk : reduced ρ μ x.val=0 := by
    change x.val-μ•greenMap ρ x.val=0
    exact sub_eq_zero.mpr (congrArg Subtype.val he).symm
  have hb := (orthogonal_mem ρ μ x.val).mp x.property x.val hk
  exact hx.2 (Subtype.ext (Classical.byContradiction
    (fun hn => (ne_of_gt (pairing_positive ρ x.val.val (fun h => hn (Subtype.ext h)))) hb)))
/-- Fredholm is applied on the actual closed C0 subspace at nonzero parameter1. -/
theorem restricted_bijective (ρ : RegularDensity) (μ : ℝ) :
    Function.Bijective (restrictedReduced ρ μ) := by
  rcases IsCompactOperator.hasEigenvalue_or_mem_resolventSet
    (𝕜 := ℝ) (X := orthogonalSpace ρ μ) (T:=restrictedOperator ρ μ)
    (restricted_compact ρ μ) (one_ne_zero : (1 : ℝ)≠0) with he|hi
  · exact (restricted_not_eigen ρ μ he).elim
  · rw [spectrum.mem_resolventSet_iff] at hi
    obtain ⟨e,he⟩:=hi
    have he_apply (x : orthogonalSpace ρ μ) : e.val x=restrictedReduced ρ μ x := by
      rw [he]
      ext q
      simp [restrictedReduced,restrictedOperator,reduced]
    have hl (x : orthogonalSpace ρ μ) : e.inv (e.val x)=x :=
      congrArg (fun A : orthogonalSpace ρ μ →L[ℝ] orthogonalSpace ρ μ => A x) e.inv_val
    have hr (x : orthogonalSpace ρ μ) : e.val (e.inv x)=x :=
      congrArg (fun A : orthogonalSpace ρ μ →L[ℝ] orthogonalSpace ρ μ => A x) e.val_inv
    exact ⟨fun x y h => (hl x).symm.trans
      ((congrArg (fun z => e.inv z) ((he_apply x).trans (h.trans (he_apply y).symm))).trans (hl y)),
      fun y => ⟨e.inv y,(he_apply (e.inv y)).symm.trans (hr y)⟩⟩
theorem solve_orthogonal (ρ : RegularDensity) (μ : ℝ) (f : Compatible ρ)
    (hf : f∈orthogonalSpace ρ μ) : ∃ u : Domain ρ,shifted ρ μ u=f.val := by
  obtain ⟨x,hx⟩ := (restricted_bijective ρ μ).2 ⟨f,hf⟩
  refine ⟨liftData ρ x.val,?_⟩
  rw [shifted_lift]
  simpa [restrictedReduced,restrictedOperator,reduced] using
    congrArg (fun v : orthogonalSpace ρ μ => v.val.val) hx
theorem modes_imply_orthogonal (ρ : RegularDensity) (μ : ℝ) (f : Compatible ρ)
    (hf : ∀ v : Domain ρ,shifted ρ μ v=0 → pairing ρ f.val v.val.val=0) :
    f∈orthogonalSpace ρ μ := by
  apply (orthogonal_mem ρ μ f).mpr
  intro k hk
  have he : k.val=μ•(greenMap ρ k).val :=
    congrArg Subtype.val (sub_eq_zero.mp (show k-μ•greenMap ρ k=0 from hk))
  have hv : shifted ρ μ (liftData ρ k)=0 :=
    (shifted_lift ρ μ k).trans (congrArg Subtype.val hk)
  have hb : pairing ρ f.val (greenMap ρ k).val=0 := hf (liftData ρ k) hv
  rw [he,pairing_smul_right,hb,mul_zero]
theorem necessary_modes (ρ : RegularDensity) (μ : ℝ) (f : Coefficient)
    (u : C2Coefficient) (hu : laplacian ρ u-μ•u.val=f)
    (v : Domain ρ) (hv : shifted ρ μ v=0) : pairing ρ f v.val.val=0 :=
  forcing_orthogonal ρ μ u v.val f (sub_eq_zero.mp hv) hu
/-- Exact normalized differential solvability, with genuine raw computational-path periods. -/
theorem solvable_iff_raw_and_modes (ρ : RegularDensity) (μ : ℝ) (f : Coefficient) :
    (∃ u : Domain ρ,shifted ρ μ u=f) ↔
      (∀ p : Trace 0 0,lineIntegral (ρ.val.val*f) (fromTrace p)=0) ∧
      (∀ v : Domain ρ,shifted ρ μ v=0 → pairing ρ f v.val.val=0) :=
  ⟨fun ⟨u,hu⟩ => ⟨(compatible_iff_raw ρ f).mp (hu ▸ shifted_compatible ρ μ u),fun v hv => necessary_modes ρ μ f u.val hu v hv⟩,
   fun ⟨hp,hm⟩ => let g : Compatible ρ := ⟨f,(compatible_iff_raw ρ f).mpr hp⟩
     solve_orthogonal ρ μ g (modes_imply_orthogonal ρ μ g hm)⟩
theorem solvable_iff_cochain_and_modes (ρ : RegularDensity) (μ : ℝ) (f : Coefficient) :
    (∃ u : Domain ρ,shifted ρ μ u=f) ↔
      (∀ p : Trace 0 0,period p (meanHarmonic (ρ.val.val*f)).val=0) ∧
      (∀ v : Domain ρ,shifted ρ μ v=0 → pairing ρ f v.val.val=0) := by
  rw [solvable_iff_raw_and_modes]
  simp only [lineIntegral_fromTrace_harmonic]
theorem zero_homogeneous (ρ : RegularDensity) (v : Domain ρ) (hv : shifted ρ 0 v=0) :
    v.val.val=0 :=
  normalized_kernel_zero ρ v (by simpa only [shifted,zero_smul,sub_zero] using hv)
/-- At zero shift there is no additional normalized-mode obstruction. -/
theorem zero_criterion (ρ : RegularDensity) (f : Coefficient) :
    (∃ u : Domain ρ,shifted ρ 0 u=f) ↔
      ∀ p : Trace 0 0,lineIntegral (ρ.val.val*f) (fromTrace p)=0 := by
  rw [solvable_iff_raw_and_modes]
  refine ⟨And.left,fun hp => ⟨hp,fun v hv => ?_⟩⟩
  rw [zero_homogeneous ρ v hv]
  simp [pairing,mean,cover]
end ComputationalHodge.ResonantRange
