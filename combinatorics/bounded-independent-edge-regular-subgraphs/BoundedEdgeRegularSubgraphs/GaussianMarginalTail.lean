module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic

/-!
# The tail of a symmetric strongly log-concave marginal
-/

public section

open MeasureTheory Set

namespace BoundedEdgeRegularSubgraphs

/-- A symmetric function with convex superlevel sets is nonincreasing
along the positive half-line. -/
theorem antitoneOn_nonneg_of_even_convex_superlevel (f : ℝ → ℝ)
    (he : ∀ x, f (-x) = f x) (hc : ∀ z, Convex ℝ {x | z ≤ f x}) :
    AntitoneOn f (Ici 0) := by
  intro x hx y _ hxy
  change 0 ≤ x at hx
  rcases eq_or_lt_of_le (hx.trans hxy) with hy | hy
  · have h : x = y := le_antisymm hxy (by linarith)
    rw [h]
  let a := (y - x) / (2 * y)
  let b := (y + x) / (2 * y)
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hxy) (by positivity)
  have hb : 0 ≤ b := div_nonneg (add_nonneg hy.le hx) (by positivity)
  have hsum : a + b = 1 := by dsimp only [a, b]; field_simp; ring
  have hpt : a • (-y) + b • y = x := by
    simp only [smul_eq_mul, a, b]
    field_simp
    ring
  have ha' : -y ∈ {t | f y ≤ f t} := by
    change f y ≤ f (-y)
    rw [he]
  have hb' : y ∈ {t | f y ≤ f t} := by change f y ≤ f y; exact le_rfl
  have h := (hc (f y)) ha' hb' ha hb hsum
  rwa [hpt] at h

/-- A Gaussian tilt that is nonincreasing on the positive half-line gives
the sharp one-sided comparison for the tail mass. -/
theorem integral_Ioi_le_of_gaussian_tilt_antitone (f : ℝ → ℝ)
    (hf : Integrable f) (h₀ : ∀ x, 0 ≤ f x) {κ r : ℝ} (hκ : 0 ≤ κ) (hr : 0 ≤ r)
    (hshape : AntitoneOn (fun x ↦ Real.exp (κ * x ^ 2 / 2) * f x) (Ici 0)) :
    (∫ x in Ioi r, f x) ≤ Real.exp (-κ * r ^ 2 / 2) * ∫ x in Ioi 0, f x := by
  let τ (x : ℝ) := x + r
  have hτ : MeasurePreserving τ (volume : Measure ℝ) volume :=
    measurePreserving_add_right volume r
  have Hτ : MeasurableEmbedding τ := (Homeomorph.addRight r).isClosedEmbedding.measurableEmbedding
  have hpre : τ ⁻¹' Ioi r = Ioi 0 := by ext x; simp [τ]
  have hchange := hτ.setIntegral_preimage_emb Hτ f (Ioi r)
  rw [hpre] at hchange
  rw [← hchange, ← integral_const_mul]
  refine setIntegral_mono_on (hτ.integrable_comp_of_integrable hf).integrableOn
    (hf.const_mul _).integrableOn measurableSet_Ioi ?_
  intro x hx
  have hx₀ : 0 ≤ x := le_of_lt hx
  have h₁ : x ∈ Ici (0 : ℝ) := hx₀
  have h₂ : x + r ∈ Ici (0 : ℝ) := add_nonneg hx₀ hr
  have h := hshape h₁ h₂ (le_add_of_nonneg_right hr)
  change Real.exp (κ * (x + r) ^ 2 / 2) * f (x + r) ≤
    Real.exp (κ * x ^ 2 / 2) * f x at h
  have he := (le_div_iff₀ (Real.exp_pos (κ * (x + r) ^ 2 / 2))).2 (by simpa only [mul_comm] using h)
  rw [mul_div_assoc, ← Real.exp_sub] at he
  have hrate : κ * x ^ 2 / 2 - κ * (x + r) ^ 2 / 2 ≤ -κ * r ^ 2 / 2 := by
    nlinarith only [mul_nonneg (mul_nonneg hκ hr) hx₀]
  simpa only [τ, mul_comm (f x)] using
    he.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrate) (h₀ x))

/-- Both tails of a symmetric Gaussian-dominated profile have mass at
most the Gaussian factor times its total mass. -/
theorem integral_abs_tail_le_of_gaussian_tilt_antitone (f : ℝ → ℝ)
    (hf : Integrable f) (h₀ : ∀ x, 0 ≤ f x) (he : ∀ x, f (-x) = f x)
    {κ r : ℝ} (hκ : 0 ≤ κ) (hr : 0 ≤ r)
    (hshape : AntitoneOn (fun x ↦ Real.exp (κ * x ^ 2 / 2) * f x) (Ici 0)) :
    (∫ x in {x | r < |x|}, f x) ≤ Real.exp (-κ * r ^ 2 / 2) * ∫ x, f x := by
  have hfabs (x : ℝ) : f |x| = f x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, he]
  let g : ℝ → ℝ := (Ioi r).indicator f
  have hg (x : ℝ) : ({x | r < |x|} : Set ℝ).indicator f x = g |x| := by
    by_cases hx : r < |x| <;> simp [g, hx, hfabs]
  have hset : MeasurableSet {x : ℝ | r < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hleft : (∫ x in {x | r < |x|}, f x) = 2 * ∫ x in Ioi r, f x := by
    rw [← integral_indicator hset]
    simp_rw [hg]
    rw [integral_comp_abs]
    change 2 * (∫ x in Ioi 0, (Ioi r).indicator f x) = _
    rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr (Ioi_subset_Ioi hr)]
  have hright : (∫ x, f x) = 2 * ∫ x in Ioi 0, f x := by
    have h := integral_comp_abs (f := f)
    simp_rw [hfabs] at h
    exact h
  rw [hleft, hright]
  have h := mul_le_mul_of_nonneg_left
    (integral_Ioi_le_of_gaussian_tilt_antitone f hf h₀ hκ hr hshape) (by norm_num : (0 : ℝ) ≤ 2)
  linarith only [h]

end BoundedEdgeRegularSubgraphs
