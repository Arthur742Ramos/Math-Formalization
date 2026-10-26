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
  · obtain ⟨e,he⟩ := spectrum.mem_resolventSet_iff.mp hi
    have he' : e.val=restrictedReduced ρ μ := by
      rw [he]
      ext x q
      simp [restrictedReduced,restrictedOperator,reduced]
    have hb : Function.Bijective e.val := (ContinuousLinearEquiv.ofUnit e).bijective
    exact he' ▸ hb
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
end ComputationalHodge.ResonantRange
