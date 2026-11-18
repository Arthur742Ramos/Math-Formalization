module

public import BoundedEdgeRegularSubgraphs.GaussianExpApproximation
import Mathlib.Analysis.Convex.Integral
import Mathlib.Tactic

/-!
# Truncating the Gaussian exponential weight
-/

public section

open MeasureTheory Set

namespace BoundedEdgeRegularSubgraphs

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- An (L^2) error for the clipped weight gives the (L^1) error for the
original weight truncated to the region where the two agree. -/
theorem integral_abs_truncated_weight_sub_le (U : Set X) (hU : MeasurableSet U)
    (w W : X → ℝ) (hW : Integrable W μ) (hEq : ∀ x ∈ U, w x = W x)
    (a b : ℝ) (hI : Integrable (fun x ↦ (W x - a) ^ 2) μ) :
    (∫ x, |U.indicator w x - b| ∂μ) ≤
      Real.sqrt (∫ x, (W x - a) ^ 2 ∂μ) + |a - b| + |b| * μ.real Uᶜ := by
  let D (x : X) := |W x - a|
  let T := Uᶜ.indicator (fun _ : X ↦ |b|)
  have hD : Integrable D μ := (hW.sub (integrable_const a)).abs
  have hD₂ : Integrable (fun x ↦ D x ^ 2) μ := by simpa only [D, sq_abs] using hI
  have hT : Integrable T μ := (integrable_const _).indicator hU.compl
  have he : U.indicator w = U.indicator W := by
    funext x
    by_cases hx : x ∈ U
    · simpa only [indicator_of_mem hx] using hEq x hx
    · simp only [indicator_of_notMem hx]
  have hg (x : X) : |U.indicator w x - b| ≤ (D x + |a - b|) + T x := by
    by_cases hx : x ∈ U
    · have hh : x ∉ Uᶜ := by simpa using hx
      rw [indicator_of_mem hx, hEq x hx, show T x = 0 from indicator_of_notMem hh _, add_zero]
      have h := abs_add_le (W x - a) (a - b)
      rw [sub_add_sub_cancel] at h
      exact h
    · rw [indicator_of_notMem hx, zero_sub, abs_neg, show T x = |b| from indicator_of_mem hx _]
      exact le_add_of_nonneg_left (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hsum : (∫ x, |U.indicator w x - b| ∂μ) ≤
      (∫ x, D x ∂μ) + |a - b| + |b| * μ.real Uᶜ := by
    let F (x : X) := D x + |a - b|
    have hF : Integrable F μ := hD.add (integrable_const _)
    have h := integral_mono (show Integrable (fun x ↦ |U.indicator w x - b|) μ by
      rw [he]; exact ((hW.indicator hU).sub (integrable_const _)).abs)
      (hF.add hT) hg
    change _ ≤ ∫ x, F x + T x ∂μ at h
    rw [integral_add hF hT] at h
    have hFint : (∫ x, F x ∂μ) = (∫ x, D x ∂μ) + |a - b| := by
      change (∫ x, D x + |a - b| ∂μ) = _
      rw [integral_add hD (integrable_const _), integral_const, probReal_univ, one_smul]
    have hTint : (∫ x, T x ∂μ) = |b| * μ.real Uᶜ := by
      change (∫ x, Uᶜ.indicator (fun _ : X ↦ |b|) x ∂μ) = _
      rw [integral_indicator hU.compl, setIntegral_const, smul_eq_mul, mul_comm]
    rwa [hFint, hTint] at h
  have hJ := (convexOn_pow (𝕜 := ℝ) 2).map_integral_le
    ((continuous_id.pow 2).continuousOn) isClosed_Ici
    (ae_of_all _ (fun x ↦ show D x ∈ Ici 0 from abs_nonneg _)) hD hD₂
  have hJ' : (∫ x, D x ∂μ) ≤ Real.sqrt (∫ x, (W x - a) ^ 2 ∂μ) := by
    apply (Real.le_sqrt (integral_nonneg fun x ↦ abs_nonneg (W x - a))
      (integral_nonneg fun x ↦ sq_nonneg (W x - a))).2
    simpa only [D, Function.comp_apply, sq_abs] using hJ
  linarith only [hJ', hsum]

/-- The difference of means after clipping is controlled by the second
moment and the mass outside the clipping set. -/
theorem abs_integral_sub_le_of_eq_on (U : Set X) (hU : MeasurableSet U)
    (f F : X → ℝ) (hf : Integrable f μ) (hF : Integrable F μ)
    (hEq : ∀ x ∈ U, f x = F x) {B s : ℝ} (hB : ∀ x, |F x| ≤ B) (hs : 0 < s)
    (hI : Integrable (fun x ↦ f x ^ 2) μ) :
    |(∫ x, F x ∂μ) - ∫ x, f x ∂μ| ≤
      (B + s / 2) * μ.real Uᶜ + (∫ x, f x ^ 2 ∂μ) / (2 * s) := by
  rw [← integral_sub hF hf]
  have heq : Uᶜ.indicator (fun x ↦ F x - f x) = fun x ↦ F x - f x := by
    funext x
    by_cases hx : x ∈ U
    · rw [indicator_of_notMem (show x ∉ Uᶜ from by simpa using hx), hEq x hx, sub_self]
    · exact indicator_of_mem (show x ∈ Uᶜ from hx) _
  rw [← heq, integral_indicator hU.compl, ← Real.norm_eq_abs]
  have hm : (∫ x in Uᶜ, (fun _ : X ↦ B + s / 2) x + f x ^ 2 / (2 * s) ∂μ) ≤
      (B + s / 2) * μ.real Uᶜ + (∫ x, f x ^ 2 ∂μ) / (2 * s) := by
    have hI' : Integrable (fun x ↦ f x ^ 2 / (2 * s)) μ := hI.div_const _
    rw [integral_add (integrable_const _) hI'.integrableOn, setIntegral_const, smul_eq_mul]
    have h := setIntegral_le_integral (s := Uᶜ) hI' (ae_of_all _ (fun x ↦ by positivity))
    simp_rw [integral_div] at h ⊢
    linarith only [h]
  refine le_trans ?_ hm
  apply norm_integral_le_of_norm_le ((integrable_const _).add (hI.div_const _)).integrableOn
  exact ae_of_all _ (fun x ↦ by
    rw [Real.norm_eq_abs]
    have hq : |f x| ≤ s / 2 + f x ^ 2 / (2 * s) := by
      suffices hk : |f x| - s / 2 ≤ f x ^ 2 / (2 * s) by linarith only [hk]
      apply (le_div_iff₀ (show 0 < 2 * s by positivity)).2
      have hh := sq_nonneg (|f x| - s)
      rw [sub_sq, sq_abs] at hh
      nlinarith only [hh]
    change |F x - f x| ≤ (B + s / 2) + f x ^ 2 / (2 * s)
    have h := abs_add_le (F x) (-f x)
    rw [← sub_eq_add_neg, abs_neg] at h
    linarith only [h, hB x, hq])

end BoundedEdgeRegularSubgraphs
