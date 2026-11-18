module

public import BoundedEdgeRegularSubgraphs.Tilt
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Scalar derivative and remainder bounds for the centring tilt
-/

@[expose] public section

namespace BoundedEdgeRegularSubgraphs

/-- The derivative of the tilted probability is its tilted Bernoulli variance. -/
theorem hasDerivAt_tiltProb (q : Set.Icc (0 : ℝ) 1) (u : ℝ) :
    HasDerivAt (fun v ↦ (tiltProb q v : ℝ))
      ((tiltProb q u : ℝ) * (1 - (tiltProb q u : ℝ))) u := by
  have hF : HasDerivAt (fun v ↦ (q : ℝ) * Real.exp v) ((q : ℝ) * Real.exp u) u :=
    (Real.hasDerivAt_exp u).const_mul (q : ℝ)
  have hN : HasDerivAt (tiltNormalizer q) ((q : ℝ) * Real.exp u) u := by
    change HasDerivAt ((fun _ : ℝ ↦ 1 - (q : ℝ)) + fun v ↦ (q : ℝ) * Real.exp v)
      ((q : ℝ) * Real.exp u) u
    simpa only [zero_add] using (hasDerivAt_const u (1 - (q : ℝ))).add hF
  have hd : (tiltProb q u : ℝ) * (1 - (tiltProb q u : ℝ)) =
      (((q : ℝ) * Real.exp u) * tiltNormalizer q u -
        ((q : ℝ) * Real.exp u) * ((q : ℝ) * Real.exp u)) / tiltNormalizer q u ^ 2 := by
    change ((q : ℝ) * Real.exp u / tiltNormalizer q u) *
        (1 - (q : ℝ) * Real.exp u / tiltNormalizer q u) = _
    field_simp [(tiltNormalizer_pos q u).ne']
  rw [hd]
  change HasDerivAt (fun v ↦ (q : ℝ) * Real.exp v / tiltNormalizer q v) _ u
  exact hF.fun_div hN (tiltNormalizer_pos q u).ne'

/-- The Bernoulli variance is a 1-Lipschitz function of the success probability. -/
theorem abs_bernoulliVariance_sub_le (p q : Set.Icc (0 : ℝ) 1) :
    |(p : ℝ) * (1 - p) - (q : ℝ) * (1 - q)| ≤ |(p : ℝ) - q| := by
  rw [show (p : ℝ) * (1 - p) - (q : ℝ) * (1 - q) =
    ((p : ℝ) - q) * (1 - p - q) by ring, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ⟨by linarith [p.property.2, q.property.2],
    by linarith [p.property.1, q.property.1]⟩)

/-- Changing the log odds by a given amount changes the success probability
by at most one quarter of that amount. -/
theorem abs_tiltProb_sub_le (q : Set.Icc (0 : ℝ) 1) (u v : ℝ) :
    |(tiltProb q u : ℝ) - tiltProb q v| ≤ (1 / 4 : ℝ) * |u - v| := by
  have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ (Set.univ : Set ℝ)) ↦ (hasDerivAt_tiltProb q x).hasDerivWithinAt)
    (C := (1 / 4 : ℝ)) (fun x _ ↦ by
      let p := tiltProb q x
      change ‖(p : ℝ) * (1 - p)‖ ≤ 1 / 4
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg p.property.1 (sub_nonneg.mpr p.property.2))]
      nlinarith only [sq_nonneg ((p : ℝ) - 1 / 2)])
    (Set.mem_univ v) (Set.mem_univ u)
  simpa only [Real.norm_eq_abs] using h

@[simp] theorem tiltProb_zero (q : Set.Icc (0 : ℝ) 1) : tiltProb q 0 = q := by
  apply Subtype.ext
  have h : tiltNormalizer q 0 = 1 := by simp [tiltNormalizer]
  simp [tiltProb, h]

/-- The nonlinear scalar remainder after linearising the tilt at zero. -/
noncomputable def tiltRemainder (q : Set.Icc (0 : ℝ) 1) (u : ℝ) : ℝ :=
  (tiltProb q u : ℝ) - q - (q : ℝ) * (1 - q) * u

@[simp] theorem tiltRemainder_zero (q : Set.Icc (0 : ℝ) 1) : tiltRemainder q 0 = 0 := by
  simp [tiltRemainder]

/-- On a bounded interval the remainder has a Lipschitz constant proportional
to the radius, as used in the centring contraction of Lemma 2.1. -/
theorem abs_tiltRemainder_sub_le (q : Set.Icc (0 : ℝ) 1) {b : ℝ} {u v : ℝ}
    (hu : |u| ≤ b) (hv : |v| ≤ b) :
    |tiltRemainder q u - tiltRemainder q v| ≤ (b / 4) * |u - v| := by
  let s := Set.Icc (-b) b
  let D (x : ℝ) := (tiltProb q x : ℝ) * (1 - (tiltProb q x : ℝ)) - (q : ℝ) * (1 - q)
  have hd (x : ℝ) : HasDerivAt (tiltRemainder q) (D x) x := by
    change HasDerivAt ((fun y ↦ (tiltProb q y : ℝ) - q) -
      fun y ↦ (q : ℝ) * (1 - q) * y) (D x) x
    exact ((hasDerivAt_tiltProb q x).sub_const (q : ℝ)).sub
      (by simpa only [mul_one, id_eq] using (hasDerivAt_id x).const_mul ((q : ℝ) * (1 - q)))
  have hD (x : ℝ) (hx : x ∈ s) : ‖D x‖ ≤ b / 4 := by
    have h := abs_tiltProb_sub_le q x 0
    rw [tiltProb_zero, sub_zero] at h
    have hx' : |x| ≤ b := abs_le.mpr hx
    rw [Real.norm_eq_abs]
    exact (abs_bernoulliVariance_sub_le _ _).trans
      (h.trans (by linarith only [hx']))
  have hu' : u ∈ s := abs_le.mp hu
  have hv' : v ∈ s := abs_le.mp hv
  have h := (convex_Icc (-b) b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ ↦ (hd x).hasDerivWithinAt) hD hv' hu'
  simpa only [Real.norm_eq_abs] using h

end BoundedEdgeRegularSubgraphs
