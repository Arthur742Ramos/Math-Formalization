module

public import BoundedEdgeRegularSubgraphs.FourierCurvature
public import BoundedEdgeRegularSubgraphs.FourierReplacement
public import BoundedEdgeRegularSubgraphs.OverlapCovariance
import Mathlib.Tactic

/-!
# The potential and its directional curvature in a Fourier box
-/

@[expose] public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The sum of the edge potentials in real phase coordinates. -/
noncomputable def degreeFourierPotential (A : Finset (Edge α))
    (q : Edge α → Set.Icc (0 : ℝ) 1) (t : α → ℝ) : ℝ :=
  ∑ e ∈ A, fourierPotential ((q e : ℝ) * (1 - q e)) (t e.val.1 + t e.val.2)

omit [Fintype α] in
theorem degreeFourierPotential_even (A : Finset (Edge α))
    (q : Edge α → Set.Icc (0 : ℝ) 1) :
    Function.Even (degreeFourierPotential A q) := by
  intro t
  simp only [degreeFourierPotential, fourierPotential, fourierEnvelope, Pi.neg_apply, ← neg_add, Real.cos_neg]

private theorem variance_bounds (q : Set.Icc (0 : ℝ) 1) :
    0 ≤ (q : ℝ) * (1 - q) ∧ (q : ℝ) * (1 - q) ≤ 1 / 4 :=
  ⟨mul_nonneg q.property.1 (sub_nonneg.mpr q.property.2),
    by nlinarith only [sq_nonneg ((q : ℝ) - 1 / 2)]⟩

/-- The Fourier modulus agrees with the exponential of the negative potential
throughout the small real box. -/
theorem degreeFourier_norm_eq_exp_neg_potential (A : Finset (Edge α))
    (q : Edge α → Set.Icc (0 : ℝ) 1) (d : α → ℤ) (t : α → ℝ)
    (ht : ∀ e ∈ A, |t e.val.1 + t e.val.2| ≤ Real.pi / 3) :
    ‖degreeFourier A q d (fun i ↦ (t i : PhaseCircle))‖ =
      Real.exp (-degreeFourierPotential A q t) := by
  rw [degreeFourier_norm_eq_phase_product, degreeFourierPotential, ← Finset.sum_neg_distrib,
    Real.exp_sum]
  apply Finset.prod_congr rfl
  intro e he
  let s := t e.val.1 + t e.val.2
  let w := (q e : ℝ) * (1 - q e)
  have hE := (half_le_fourierPotentialCurvature (variance_bounds (q e)).1
    (variance_bounds (q e)).2 (ht e he)).1
  rw [← AddCircle.coe_add, phaseBernoulliFactor, fourier_one_coe]
  change ‖bernoulliFourierFactor (q e) s‖ = Real.exp (-fourierPotential w s)
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.exp_nonneg _)).mp
  rw [← fourierEnvelope_eq_norm_sq, pow_two (Real.exp _), ← Real.exp_add]
  have heq : -fourierPotential w s + -fourierPotential w s = Real.log (fourierEnvelope w s) := by
    unfold fourierPotential
    ring
  rw [heq, Real.exp_log hE]

omit [Fintype α] in
/-- The first derivative along a line in real phase coordinates. -/
theorem hasDerivAt_degreeFourierPotential_line (A : Finset (Edge α))
    (q : Edge α → Set.Icc (0 : ℝ) 1) (t v : α → ℝ) (x : ℝ)
    (ht : ∀ e ∈ A, |(t e.val.1 + t e.val.2) + x * (v e.val.1 + v e.val.2)| ≤ Real.pi / 3) :
    HasDerivAt (fun s ↦ degreeFourierPotential A q (fun i ↦ t i + s * v i))
      (∑ e ∈ A, fourierPotentialSlope ((q e : ℝ) * (1 - q e))
        ((t e.val.1 + t e.val.2) + x * (v e.val.1 + v e.val.2)) * (v e.val.1 + v e.val.2)) x := by
  unfold degreeFourierPotential
  apply HasDerivAt.fun_sum
  intro e he
  let w := (q e : ℝ) * (1 - q e)
  let a := t e.val.1 + t e.val.2
  let b := v e.val.1 + v e.val.2
  have hL : HasDerivAt (fun s ↦ a + s * b) b x := by
    simpa only [one_mul, id_eq] using ((hasDerivAt_id x).mul_const b).const_add a
  have hE := (half_le_fourierPotentialCurvature (variance_bounds (q e)).1
    (variance_bounds (q e)).2 (ht e he)).1
  have h := (hasDerivAt_fourierPotential w (a + x * b) hE).comp x hL
  convert h using 1
  funext s
  dsimp [a, b]
  congr 1
  ring

omit [Fintype α] in
/-- The second derivative along the same line is the weighted sum of squared
endpoint increments. -/
theorem hasDerivAt_degreeFourierPotential_slope_line (A : Finset (Edge α))
    (q : Edge α → Set.Icc (0 : ℝ) 1) (t v : α → ℝ) (x : ℝ)
    (ht : ∀ e ∈ A, |(t e.val.1 + t e.val.2) + x * (v e.val.1 + v e.val.2)| ≤ Real.pi / 3) :
    HasDerivAt (fun s ↦ ∑ e ∈ A, fourierPotentialSlope ((q e : ℝ) * (1 - q e))
      ((t e.val.1 + t e.val.2) + s * (v e.val.1 + v e.val.2)) * (v e.val.1 + v e.val.2))
      (∑ e ∈ A, fourierPotentialCurvature ((q e : ℝ) * (1 - q e))
        ((t e.val.1 + t e.val.2) + x * (v e.val.1 + v e.val.2)) * (v e.val.1 + v e.val.2) ^ 2) x := by
  apply HasDerivAt.fun_sum
  intro e he
  let w := (q e : ℝ) * (1 - q e)
  let a := t e.val.1 + t e.val.2
  let b := v e.val.1 + v e.val.2
  have hL : HasDerivAt (fun s ↦ a + s * b) b x := by
    simpa only [one_mul, id_eq] using ((hasDerivAt_id x).mul_const b).const_add a
  have hE := (half_le_fourierPotentialCurvature (variance_bounds (q e)).1
    (variance_bounds (q e)).2 (ht e he)).1
  have h := ((hasDerivAt_fourierPotentialSlope w (a + x * b) hE).comp x hL).mul_const b
  change HasDerivAt (fun s ↦ fourierPotentialSlope w (a + s * b) * b)
    (fourierPotentialCurvature w (a + x * b) * b ^ 2) x
  simpa only [Function.comp_apply, pow_two, mul_assoc] using h

/-- The curvature lower bound for the full and deleted-clique boxes in Lemma B.1. -/
theorem degreeFourierPotential_curvature_lower (S : Finset α)
    (hm : 3 ≤ ((Finset.univ : Finset α) \ S).card)
    (q : Edge α → Set.Icc (0 : ℝ) 1) (t v : α → ℝ)
    {l : ℝ} (hl : 0 ≤ l) (hq : ∀ e, l ≤ (q e : ℝ) * (1 - q e))
    (ht : ∀ e ∈ edgesOutsideOverlap S, |t e.val.1 + t e.val.2| ≤ Real.pi / 3) :
    l * ((((Finset.univ : Finset α) \ S).card : ℝ) ^ 2 / (3 * Fintype.card α)) / 2 *
      (∑ i, v i ^ 2) ≤
      ∑ e ∈ edgesOutsideOverlap S, fourierPotentialCurvature
        ((q e : ℝ) * (1 - q e)) (t e.val.1 + t e.val.2) * (v e.val.1 + v e.val.2) ^ 2 := by
  have h := (degreeCovariance_outside_overlap_bounds S hm q l hl hq v).1
  rw [degreeCovariance_quadratic] at h
  calc
    _ ≤ ((∑ e ∈ edgesOutsideOverlap S,
      ((q e : ℝ) * (1 - q e)) * (v e.val.1 + v e.val.2) ^ 2) / 2) := by linarith only [h]
    _ ≤ _ := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro e he
      rw [mul_div_right_comm]
      exact mul_le_mul_of_nonneg_right
        (half_le_fourierPotentialCurvature (variance_bounds (q e)).1
          (variance_bounds (q e)).2 (ht e he)).2 (sq_nonneg _)

end BoundedEdgeRegularSubgraphs
