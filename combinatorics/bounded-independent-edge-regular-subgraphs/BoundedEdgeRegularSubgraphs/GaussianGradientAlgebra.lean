module

public import BoundedEdgeRegularSubgraphs.GaussianCubicStein
import Mathlib.Tactic

/-!
# Differentiating the cubic gradient product
-/

public section

open Matrix MvPolynomial
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

private theorem pderiv_cubic_sum {n : ℕ} {ι : Type*}
    (A : Finset ι) (a : ι → ℝ) (v : ι → Fin n → ℝ) (j : Fin n) :
    pderiv j (gaussianCubicPolynomial A a v) =
      ∑ e ∈ A, C (3 * a e * v e j) * linearPolynomial (v e) ^ 2 := by
  simp only [gaussianCubicPolynomial, map_sum, pderiv_C_mul, pderiv_pow, pderiv_linearPolynomial,
    Nat.reduceSub, map_mul]
  apply Finset.sum_congr rfl
  intro e _
  have he : (C (3 : ℝ) : MvPolynomial (Fin n) ℝ) = ((3 : ℕ) : MvPolynomial (Fin n) ℝ) := by
    norm_num only [map_ofNat, Nat.cast_ofNat]
  rw [he]
  ring

private theorem eval_pderiv_square_sum {n : ℕ} {ι : Type*}
    (A : Finset ι) (a c : ι → ℝ) (v : ι → Fin n → ℝ) (i : Fin n) (x : Fin n → ℝ) :
    eval x (pderiv i (∑ e ∈ A, C (a e) * (linearPolynomial (v e) ^ 2 + C (c e)))) =
      ∑ e ∈ A, a e * (2 * (v e ⬝ᵥ x) * v e i) := by
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [pderiv_C_mul, map_add, pderiv_C, add_zero, pderiv_pow, pderiv_linearPolynomial]
  norm_num only [map_mul, map_ofNat, map_natCast, eval_C, eval_linearPolynomial, Nat.reduceSub, pow_one]

private theorem sum_dual_proj_eq {n : ℕ} {ι : Type*}
    (A : Finset ι) (v : ι → Fin n → ℝ) (a : ι → ℝ) (p : Fin n → ℝ) :
    (∑ j, (∑ e ∈ A, a e * v e j) * p j) = ∑ e ∈ A, a e * (v e ⬝ᵥ p) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ ↦ by ring)

/-- The derivative of the gradient product is a linear combination of
the edge vectors, with coefficients given by covariance row sums. -/
theorem eval_pderiv_gaussianCubic_gradientProduct {n : ℕ} {ι : Type*}
    (A : Finset ι) (a : ι → ℝ) (v : ι → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    let F := gaussianCubicPolynomial A a v
    let G := gaussianCubicAuxiliary A a v
    let Y := fun e ↦ v e ⬝ᵥ x
    let D := fun e ↦ ∑ j, v e j ^ 2
    let R := fun e ↦ ∑ h ∈ A, (a h * (v e ⬝ᵥ v h)) * (Y h ^ 2 + D h)
    eval x (pderiv i (gaussianGradientProduct F G)) =
      ∑ e ∈ A, (12 * a e * Y e * R e) * v e i := by
  let F := gaussianCubicPolynomial A a v
  let G := gaussianCubicAuxiliary A a v
  let Y (e : ι) := v e ⬝ᵥ x
  let D (e : ι) := ∑ j, v e j ^ 2
  let R (e : ι) := ∑ h ∈ A, (a h * (v e ⬝ᵥ v h)) * (Y h ^ 2 + D h)
  let F₁ (j : Fin n) := eval x (pderiv j F)
  let G₁ (j : Fin n) := eval x (pderiv j G)
  let b (e : ι) := a e * Y e * v e i
  have hF₁ (j : Fin n) : F₁ j = ∑ e ∈ A, (3 * a e * Y e ^ 2) * v e j :=
    eval_pderiv_gaussianCubicPolynomial A a v x j
  have hG₁ (j : Fin n) : G₁ j = ∑ e ∈ A, (a e * (Y e ^ 2 + 2 * D e)) * v e j := by
    change eval x (pderiv j G) = _
    rw [pderiv_gaussianCubicAuxiliary]
    simp only [map_sum, map_mul, map_pow, map_add, eval_C, eval_linearPolynomial]
    exact Finset.sum_congr rfl (fun e _ ↦ by dsimp only [Y, D]; ring)
  have hF₂ (j : Fin n) : eval x (pderiv i (pderiv j F)) = ∑ e ∈ A, (6 * b e) * v e j := by
    rw [pderiv_cubic_sum]
    have h : (∑ e ∈ A, C (3 * a e * v e j) * linearPolynomial (v e) ^ 2) =
        ∑ e ∈ A, C (3 * a e * v e j) * (linearPolynomial (v e) ^ 2 + C 0) := by
      simp only [map_zero, add_zero]
    rw [h, eval_pderiv_square_sum]
    exact Finset.sum_congr rfl (fun e _ ↦ by dsimp only [b, Y]; ring)
  have hG₂ (j : Fin n) : eval x (pderiv i (pderiv j G)) = ∑ e ∈ A, (2 * b e) * v e j := by
    rw [pderiv_gaussianCubicAuxiliary, eval_pderiv_square_sum]
    exact Finset.sum_congr rfl (fun e _ ↦ by dsimp only [b, Y]; ring)
  have hRow (e : ι) : 6 * (v e ⬝ᵥ G₁) + 2 * (v e ⬝ᵥ F₁) = 12 * R e := by
    have hcombined (j : Fin n) :
        6 * G₁ j + 2 * F₁ j = ∑ h ∈ A, (12 * a h * (Y h ^ 2 + D h)) * v h j := by
      rw [hG₁, hF₁, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
    calc
      _ = ∑ j, (6 * G₁ j + 2 * F₁ j) * v e j := by
        simp only [dotProduct, Finset.mul_sum, Finset.sum_add_distrib, add_mul]
        congr 1 <;> exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
      _ = ∑ h ∈ A, (12 * a h * (Y h ^ 2 + D h)) * (v h ⬝ᵥ v e) := by
        simp_rw [hcombined]
        exact sum_dual_proj_eq A v _ (v e)
      _ = _ := by
        dsimp only [R]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun h _ ↦ by rw [dotProduct_comm (v h) (v e)]; ring)
  change eval x (pderiv i (gaussianGradientProduct F G)) = ∑ e ∈ A, (12 * a e * Y e * R e) * v e i
  calc
    _ = (∑ j, (∑ e ∈ A, (6 * b e) * v e j) * G₁ j) +
        ∑ j, (∑ e ∈ A, (2 * b e) * v e j) * F₁ j := by
      simp only [gaussianGradientProduct, map_sum, pderiv_mul, map_add, map_mul,
        Finset.sum_add_distrib, hF₂, hG₂, F₁, G₁]
      congr 1 <;> exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
    _ = _ := by
      rw [sum_dual_proj_eq, sum_dual_proj_eq, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      calc
        _ = b e * (6 * (v e ⬝ᵥ G₁) + 2 * (v e ⬝ᵥ F₁)) := by ring
        _ = _ := by rw [hRow]; dsimp only [b]; ring

end BoundedEdgeRegularSubgraphs
