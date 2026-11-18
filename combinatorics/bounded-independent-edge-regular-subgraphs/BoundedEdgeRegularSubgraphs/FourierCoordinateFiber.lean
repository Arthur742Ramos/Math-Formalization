module

public import BoundedEdgeRegularSubgraphs.FourierFiber
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Integrating the exceptional-coordinate bound over all fibres
-/

public section

open MeasureTheory

namespace BoundedEdgeRegularSubgraphs

/-- A comparison between the exceptional part of each fibre and its
permitted replacements bounds the integral over the entire exceptional set. -/
theorem integral_prod_region_le_of_replacement {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : X × Y → ℝ)
    (hf : Integrable f (μ.prod ν)) (h₀ : ∀ z, 0 ≤ f z)
    (S : Set (X × Y)) (hS : MeasurableSet S) {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (h : ∀ y : Y, ∃ R : Set X, MeasurableSet R ∧ δ ≤ μ.real R ∧
      ∀ x z : X, (x, y) ∈ S → z ∈ R → f (x, y) ≤ c * f (z, y)) :
    (∫ z in S, f z ∂μ.prod ν) ≤ (c / δ) * ∫ z, f z ∂μ.prod ν := by
  let g := S.indicator f
  have hg : Integrable g (μ.prod ν) := hf.indicator hS
  have hleft : (∫ z in S, f z ∂μ.prod ν) = ∫ y, ∫ x, g (x, y) ∂μ ∂ν := by
    rw [← integral_indicator hS]
    exact integral_prod_symm g hg
  rw [hleft, integral_prod_symm f hf, ← integral_const_mul]
  have hgi : Integrable (fun y ↦ ∫ x, g (x, y) ∂μ) ν := hg.integral_prod_right
  have hfi : Integrable (fun y ↦ ∫ x, f (x, y) ∂μ) ν := hf.integral_prod_right
  apply integral_mono_ae hgi (hfi.const_mul _)
  filter_upwards [hf.prod_left_ae] with y hy
  let T : Set X := (fun x : X ↦ (x, y)) ⁻¹' S
  have hT : MeasurableSet T := hS.preimage (measurable_id.prodMk measurable_const)
  obtain ⟨R, hR, hRμ, hcompare⟩ := h y
  have hp : 0 < μ.real R := hδ.trans_le hRμ
  have hh := integral_fibre_le_of_replacement μ (fun x ↦ f (x, y)) hy
    (fun x ↦ h₀ (x, y)) T R hT hR hp hc
    (fun x hx z hz ↦ hcompare x z hx hz)
  have hsect : (fun x ↦ g (x, y)) = T.indicator (fun x ↦ f (x, y)) := by
    funext x
    by_cases hx : (x, y) ∈ S
    · have hx' : x ∈ T := hx
      simp only [g, Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    · have hx' : x ∉ T := hx
      simp only [g, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']
  simp_rw [hsect, integral_indicator hT]
  exact hh.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hc hδ hRμ)
    (integral_nonneg fun x ↦ h₀ (x, y)))

end BoundedEdgeRegularSubgraphs
