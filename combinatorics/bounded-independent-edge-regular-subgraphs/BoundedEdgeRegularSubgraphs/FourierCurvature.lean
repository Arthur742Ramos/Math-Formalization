module

public import BoundedEdgeRegularSubgraphs.BernoulliFourier
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# Curvature of the scalar Fourier potential near a mode
-/

@[expose] public section

namespace BoundedEdgeRegularSubgraphs

/-- The squared Fourier modulus written in terms of the Bernoulli variance. -/
noncomputable def fourierEnvelope (w s : ℝ) : ℝ := 1 - 2 * w + 2 * w * Real.cos s

/-- The contribution of an edge to the negative log-modulus. -/
noncomputable def fourierPotential (w s : ℝ) : ℝ := -(1 / 2 : ℝ) * Real.log (fourierEnvelope w s)

noncomputable def fourierPotentialSlope (w s : ℝ) : ℝ :=
  w * Real.sin s / fourierEnvelope w s

noncomputable def fourierPotentialCurvature (w s : ℝ) : ℝ :=
  w * Real.cos s / fourierEnvelope w s +
    2 * w ^ 2 * Real.sin s ^ 2 / (fourierEnvelope w s) ^ 2

theorem fourierEnvelope_eq_norm_sq (q s : ℝ) :
    fourierEnvelope (q * (1 - q)) s = ‖bernoulliFourierFactor q s‖ ^ 2 := by
  rw [bernoulliFourierFactor_norm_sq, fourierEnvelope,
    show Real.cos s = 1 - 2 * Real.sin (s / 2) ^ 2 by
      nth_rw 1 [show s = 2 * (s / 2) by ring]
      exact Real.cos_two_mul_eq_one_sub _]
  ring

private theorem hasDerivAt_fourierEnvelope (w s : ℝ) :
    HasDerivAt (fourierEnvelope w) (-2 * w * Real.sin s) s := by
  change HasDerivAt ((fun _ : ℝ ↦ 1 - 2 * w) + (fun u ↦ 2 * w * Real.cos u)) _ s
  have h := (hasDerivAt_const s (1 - 2 * w)).add ((Real.hasDerivAt_cos s).const_mul (2 * w))
  convert h using 1
  ring

/-- The first derivative of the edge potential wherever the modulus is positive. -/
theorem hasDerivAt_fourierPotential (w s : ℝ) (hs : 0 < fourierEnvelope w s) :
    HasDerivAt (fourierPotential w) (fourierPotentialSlope w s) s := by
  unfold fourierPotential
  have h := ((hasDerivAt_fourierEnvelope w s).log hs.ne').const_mul (-(1 / 2 : ℝ))
  convert h using 1
  unfold fourierPotentialSlope
  ring

/-- The exact second derivative formula from the small-box argument in Lemma B.1. -/
theorem hasDerivAt_fourierPotentialSlope (w s : ℝ) (hs : 0 < fourierEnvelope w s) :
    HasDerivAt (fourierPotentialSlope w) (fourierPotentialCurvature w s) s := by
  show HasDerivAt (fun u ↦ w * Real.sin u / fourierEnvelope w u) _ s
  have h := ((Real.hasDerivAt_sin s).const_mul w).fun_div
    (hasDerivAt_fourierEnvelope w s) hs.ne'
  convert h using 1
  unfold fourierPotentialCurvature
  field_simp [hs.ne']
  ring

/-- Near zero the edge potential has second derivative at least half the variance. -/
theorem half_le_fourierPotentialCurvature {w s : ℝ}
    (hw : 0 ≤ w) (hw' : w ≤ 1 / 4) (hs : |s| ≤ Real.pi / 3) :
    0 < fourierEnvelope w s ∧ w / 2 ≤ fourierPotentialCurvature w s := by
  have hcos : 1 / 2 ≤ Real.cos s := by
    rw [← Real.cos_pi_div_three, ← Real.cos_abs s]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg s)
      (by linarith [Real.pi_pos]) hs
  have hden_le : fourierEnvelope w s ≤ 1 := by
    unfold fourierEnvelope
    nlinarith only [mul_nonneg hw (sub_nonneg.mpr (Real.cos_le_one s))]
  have hden : 0 < fourierEnvelope w s := by
    unfold fourierEnvelope
    nlinarith only [hw, hw', mul_nonneg hw (sub_nonneg.mpr hcos)]
  refine ⟨hden, ?_⟩
  unfold fourierPotentialCurvature
  apply le_add_of_le_of_nonneg _ (by positivity)
  apply (le_div_iff₀ hden).mpr
  have h₁ := mul_le_of_le_one_right (by positivity : 0 ≤ w / 2) hden_le
  have h₂ := mul_le_mul_of_nonneg_left hcos hw
  linarith only [h₁, h₂]

end BoundedEdgeRegularSubgraphs
