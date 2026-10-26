module
public import CompactGreen
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
@[expose] public section
namespace ComputationalHodge.CircleFredholm
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson
open ComputationalHodge.GreenOperator ComputationalHodge.CompactGreen
open ComputationalHodge.ACLifts ComputationalHodge.TraceIntegrals
open MeasureTheory Set Function Topology Module
open scoped Topology NNReal unitInterval ContDiff

/-- Actual normalized twice continuously differentiable circle functions; no Banach claim. -/
abbrev Domain (ρ : RegularDensity) := {u : C2Coefficient // weightedMean ρ u.val=0}
noncomputable def laplaceData (ρ : RegularDensity) (u : Domain ρ) : Compatible ρ :=
  ⟨laplacian ρ u.val,weightedMean_laplacian ρ u.val⟩
noncomputable def liftData (ρ : RegularDensity) (f : Compatible ρ) : Domain ρ :=
  ⟨solution ρ f,solution_mean_zero ρ f⟩
noncomputable def reduced (ρ : RegularDensity) (μ : ℝ) : Compatible ρ →L[ℝ] Compatible ρ :=
  1-μ•greenMap ρ
noncomputable def shifted (ρ : RegularDensity) (μ : ℝ) (u : Domain ρ) : Coefficient :=
  laplacian ρ u.val-μ•u.val.val
/-- Resonance is an actual nonzero normalized C2 solution, not an abstract assumption. -/
def Resonant (ρ : RegularDensity) (μ : ℝ) : Prop :=
  ∃ u : Domain ρ,u.val.val≠0 ∧ shifted ρ μ u=0

theorem laplace_lift (ρ : RegularDensity) (f : Compatible ρ) : laplaceData ρ (liftData ρ f)=f :=
  Subtype.ext (solution_solves ρ f)
theorem lift_laplace (ρ : RegularDensity) (u : Domain ρ) : liftData ρ (laplaceData ρ u)=u :=
  Subtype.ext (normalized_unique ρ _ _ (solution_solves ρ (laplaceData ρ u))
    (solution_mean_zero ρ _) u.property)
theorem green_laplace (ρ : RegularDensity) (u : Domain ρ) :
    (greenMap ρ (laplaceData ρ u)).val=u.val.val :=
  congrArg (fun v : Domain ρ => v.val.val) (lift_laplace ρ u)
theorem shifted_lift (ρ : RegularDensity) (μ : ℝ) (f : Compatible ρ) :
    shifted ρ μ (liftData ρ f)=(reduced ρ μ f).val := by
  change laplacian ρ (solution ρ f)-μ•(solution ρ f).val=f.val-μ•(solution ρ f).val
  rw [solution_solves]
theorem equation_iff (ρ : RegularDensity) (μ : ℝ) (u : Domain ρ) (f : Compatible ρ) :
    shifted ρ μ u=f.val ↔ reduced ρ μ (laplaceData ρ u)=f := by
  have he : shifted ρ μ u=(reduced ρ μ (laplaceData ρ u)).val := by
    rw [← shifted_lift,lift_laplace]
  rw [he]
  exact Subtype.ext_iff.symm

theorem eigen_to_resonant (ρ : RegularDensity) (μ : ℝ)
    (h : Module.End.HasEigenvalue (μ•greenMap ρ : Compatible ρ →L[ℝ] Compatible ρ).toLinearMap 1) :
    Resonant ρ μ := by
  obtain ⟨f,hf⟩:=h.exists_hasEigenvector
  have he : μ•greenMap ρ f=f := by simpa using hf.apply_eq_smul
  refine ⟨liftData ρ f,?_,?_⟩
  · intro hz
    change (greenMap ρ f).val=0 at hz
    apply hf.2
    rw [← he]
    exact Subtype.ext (by change μ•(greenMap ρ f).val=0;rw [hz,smul_zero])
  · rw [shifted_lift]
    change f.val-μ•(greenMap ρ f).val=0
    exact sub_eq_zero.mpr (congrArg Subtype.val he).symm

theorem shifted_compatible (ρ : RegularDensity) (μ : ℝ) (u : Domain ρ) :
    shifted ρ μ u∈compatibleSpace ρ :=
  (compatibleSpace ρ).sub_mem (weightedMean_laplacian ρ u.val)
    ((compatibleSpace ρ).smul_mem μ u.property)
/-- Stock compact-operator Fredholm theory is applied at nonzero spectral parameter1. -/
theorem reduced_bijective (ρ : RegularDensity) (μ : ℝ) (h : ¬Resonant ρ μ) :
    Function.Bijective (reduced ρ μ) := by
  have hc : IsCompactOperator (μ•greenMap ρ : Compatible ρ →L[ℝ] Compatible ρ) :=
    (green_isCompactOperator ρ).smul μ
  rcases IsCompactOperator.hasEigenvalue_or_mem_resolventSet (𝕜 := ℝ) (X := Compatible ρ) (T:=μ•greenMap ρ) hc (one_ne_zero : (1 : ℝ)≠0) with he|hi
  · exact (h (eigen_to_resonant ρ μ he)).elim
  · rw [spectrum.mem_resolventSet_iff] at hi
    apply (ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℝ) (E := Compatible ρ)).mp
    simpa [reduced] using hi

noncomputable def reducedEquiv (ρ : RegularDensity) (μ : ℝ) (h : ¬Resonant ρ μ) :
    Compatible ρ ≃L[ℝ] Compatible ρ :=
  ContinuousLinearEquiv.ofBijective (𝕜 := ℝ) (𝕜' := ℝ) (E := Compatible ρ) (F := Compatible ρ) (reduced ρ μ)
    (LinearMap.ker_eq_bot.mpr (reduced_bijective ρ μ h).1)
    (LinearMap.range_eq_top.mpr (reduced_bijective ρ μ h).2)
theorem inverse_solves (ρ : RegularDensity) (μ : ℝ) (h : ¬Resonant ρ μ) (f : Compatible ρ) :
    reduced ρ μ ((reducedEquiv ρ μ h).symm f)=f :=
  (reducedEquiv ρ μ h).apply_symm_apply f

theorem unique_solvability (ρ : RegularDensity) (μ : ℝ) (h : ¬Resonant ρ μ)
    (f : Compatible ρ) : ∃! u : Domain ρ,shifted ρ μ u=f.val := ⟨liftData ρ ((reducedEquiv ρ μ h).symm f),
    (shifted_lift ρ μ _).trans (congrArg Subtype.val (inverse_solves ρ μ h f)),
    fun u hu => (lift_laplace ρ u).symm.trans (congrArg (liftData ρ)
      ((reduced_bijective ρ μ h).1 (((equation_iff ρ μ u f).mp hu).trans (inverse_solves ρ μ h f).symm)))⟩

theorem resonance_not_unique (ρ : RegularDensity) (μ : ℝ) (h : Resonant ρ μ) :
    ¬∀ f : Compatible ρ,∃! u : Domain ρ,shifted ρ μ u=f.val := by
  obtain ⟨u,hn,hu⟩ := h
  exact fun hs => hn ((congrArg (fun a : Domain ρ => a.val.val)
    ((hs 0).unique (y₂ := liftData ρ 0) hu (by rw [shifted_lift];simp [reduced]))).trans
      (congrArg Subtype.val (map_zero (greenMap ρ))))

/-- Exactly one branch, expressed with both disjunction and mutual exclusion. -/
theorem fredholm_alternative (ρ : RegularDensity) (μ : ℝ) :
    (Resonant ρ μ ∨ ∀ f : Compatible ρ,∃! u : Domain ρ,shifted ρ μ u=f.val) ∧
    ¬(Resonant ρ μ ∧ ∀ f : Compatible ρ,∃! u : Domain ρ,shifted ρ μ u=f.val) := ⟨(Classical.em _).elim Or.inl (fun h => Or.inr (unique_solvability ρ μ h)),
    fun h => resonance_not_unique ρ μ h.1 h.2⟩

theorem zero_nonresonant (ρ : RegularDensity) : ¬Resonant ρ 0 := fun ⟨u,hn,hu⟩ => hn ((green_laplace ρ u).symm.trans
    ((congrArg (fun f : Compatible ρ => (greenMap ρ f).val)
      (Subtype.ext (show laplacian ρ u.val=0 from by simpa [shifted] using hu))).trans
        (congrArg Subtype.val (map_zero (greenMap ρ)))))

/-- Actual bounded solution map on H, constructed from the proved reduced inverse. -/
noncomputable def boundedSolution (ρ : RegularDensity) (μ : ℝ) (h : ¬Resonant ρ μ) :
    Compatible ρ →L[ℝ] Compatible ρ :=
  (greenMap ρ).comp (reducedEquiv ρ μ h).symm.toContinuousLinearMap
theorem boundedSolution_regular (ρ : RegularDensity) (μ : ℝ) (h : ¬Resonant ρ μ)
    (f : Compatible ρ) : ContDiff ℝ 2 (cover (boundedSolution ρ μ h f).val) :=
  greenMap_regular ρ _
theorem boundedSolution_solves (ρ : RegularDensity) (μ : ℝ) (h : ¬Resonant ρ μ)
    (f : Compatible ρ) :
    ∃ u : Domain ρ,u.val.val=(boundedSolution ρ μ h f).val ∧ shifted ρ μ u=f.val :=
  ⟨liftData ρ ((reducedEquiv ρ μ h).symm f),rfl,by rw [shifted_lift,inverse_solves]⟩
theorem boundedSolution_stability (ρ : RegularDensity) (μ : ℝ) (h : ¬Resonant ρ μ) :
    ∃ C : ℝ,0≤C ∧ ∀ f g : Compatible ρ,
      ‖boundedSolution ρ μ h f-boundedSolution ρ μ h g‖≤C*‖f-g‖ :=
by
  obtain ⟨C,hC,hb⟩ := ContinuousLinearMap.bound (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := Compatible ρ) (F := Compatible ρ) (σ₁₂ := RingHom.id ℝ) (boundedSolution ρ μ h)
  exact ⟨C,hC.le,fun f g => by simpa only [map_sub] using hb (f-g)⟩
theorem boundedSolution_zero (ρ : RegularDensity) :
    boundedSolution ρ 0 (zero_nonresonant ρ)=greenMap ρ := ContinuousLinearMap.ext (fun f => congrArg (greenMap ρ)
    (by simpa [reduced] using inverse_solves ρ 0 (zero_nonresonant ρ) f))

theorem boundedSolution_periods (ρ : RegularDensity) (μ : ℝ) (h : ¬Resonant ρ μ)
    (f : Compatible ρ) :
    (∀ p : Trace 0 0,lineIntegral (ρ.val.val*(boundedSolution ρ μ h f).val) (fromTrace p)=0) ∧
    (∀ p : Trace 0 0,period p (meanHarmonic (ρ.val.val*(boundedSolution ρ μ h f).val)).val=0) :=
  ⟨(compatible_iff_raw ρ _).mp (boundedSolution ρ μ h f).property,
   (compatible_iff_periods ρ _).mp (boundedSolution ρ μ h f).property⟩
/-- Outside resonance the actual raw computational periods are necessary and sufficient. -/
theorem solvable_iff_raw_periods (ρ : RegularDensity) (μ : ℝ) (h : ¬Resonant ρ μ)
    (f : Coefficient) :
    (∃ u : Domain ρ,shifted ρ μ u=f) ↔
      ∀ p : Trace 0 0,lineIntegral (ρ.val.val*f) (fromTrace p)=0 := ⟨fun ⟨u,hu⟩ => (compatible_iff_raw ρ _).mp (hu ▸ shifted_compatible ρ μ u),
    fun hf => (unique_solvability ρ μ h ⟨f,(compatible_iff_raw ρ f).mpr hf⟩).exists⟩

end ComputationalHodge.CircleFredholm
