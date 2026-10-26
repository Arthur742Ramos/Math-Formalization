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
theorem lift_laplace (ρ : RegularDensity) (u : Domain ρ) : liftData ρ (laplaceData ρ u)=u :=
  Subtype.ext (normalized_unique ρ _ _ (solution_solves ρ (laplaceData ρ u))
    (solution_mean_zero ρ _) u.property)
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
end ComputationalHodge.CircleFredholm
