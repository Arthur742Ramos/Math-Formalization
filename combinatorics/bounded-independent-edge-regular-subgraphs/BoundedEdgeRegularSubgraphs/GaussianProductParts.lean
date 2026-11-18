module

public import BoundedEdgeRegularSubgraphs.GaussianMoments
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Coordinate integration by parts for independent normal variables
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace BoundedEdgeRegularSubgraphs

/-- The joint law of independent standard real Gaussian coordinates. -/
noncomputable def standardGaussianProduct (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ ↦ gaussianReal 0 1

instance (n : ℕ) : IsProbabilityMeasure (standardGaussianProduct n) := by
  unfold standardGaussianProduct
  infer_instance

/-- Gaussian integration by parts in one coordinate of an independent
standard Gaussian vector. The derivative is along the corresponding slice. -/
theorem integral_standardGaussianProduct_partial {n : ℕ} (i : Fin (n + 1))
    (F D : (Fin (n + 1) → ℝ) → ℝ)
    (hd : ∀ y : Fin n → ℝ, ∀ t : ℝ,
      HasDerivAt (fun s : ℝ ↦ F (i.insertNth s y)) (D (i.insertNth t y)) t)
    (hF : Integrable F (standardGaussianProduct (n + 1)))
    (hD : Integrable D (standardGaussianProduct (n + 1)))
    (hX : Integrable (fun x ↦ x i * F x) (standardGaussianProduct (n + 1))) :
    (∫ x, D x ∂standardGaussianProduct (n + 1)) =
      ∫ x, x i * F x ∂standardGaussianProduct (n + 1) := by
  let σ := gaussianReal 0 1
  let ν := standardGaussianProduct n
  have : IsProbabilityMeasure ν := inferInstanceAs
    (IsProbabilityMeasure (standardGaussianProduct n))
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i
  have he : MeasurePreserving e (standardGaussianProduct (n + 1)) (σ.prod ν) :=
    measurePreserving_piFinSuccAbove (fun _ ↦ σ) i
  have hs := he.symm e
  let F' (z : ℝ × (Fin n → ℝ)) := F (e.symm z)
  let D' (z : ℝ × (Fin n → ℝ)) := D (e.symm z)
  let X' (z : ℝ × (Fin n → ℝ)) := (e.symm z) i * F (e.symm z)
  have hF' : Integrable F' (σ.prod ν) := hs.integrable_comp_of_integrable hF
  have hD' : Integrable D' (σ.prod ν) := hs.integrable_comp_of_integrable hD
  have hX' : Integrable X' (σ.prod ν) := hs.integrable_comp_of_integrable hX
  rw [← hs.integral_comp' D, ← hs.integral_comp' (fun x ↦ x i * F x)]
  change (∫ z, D' z ∂σ.prod ν) = ∫ z, X' z ∂σ.prod ν
  rw [integral_prod_symm D' hD', integral_prod_symm X' hX']
  apply integral_congr_ae
  filter_upwards [hF'.swap.prod_right_ae, hD'.swap.prod_right_ae, hX'.swap.prod_right_ae]
    with y hFy hDy hXy
  change Integrable (fun t ↦ F (e.symm (t, y))) σ at hFy
  change Integrable (fun t ↦ D (e.symm (t, y))) σ at hDy
  change Integrable (fun t ↦ (e.symm (t, y)) i * F (e.symm (t, y))) σ at hXy
  have he' (t : ℝ) : e.symm (t, y) = i.insertNth t y := rfl
  simpa only [F', D', X', he', Fin.insertNth_apply_same] using
    integral_gaussianReal_deriv_eq_mul (fun t ↦ F (i.insertNth t y))
      (fun t ↦ D (i.insertNth t y)) (hd y)
      (by simpa only [he'] using hFy)
      (by simpa only [he'] using hDy)
      (by simpa only [he', Fin.insertNth_apply_same] using hXy)

end BoundedEdgeRegularSubgraphs
