module

public import BoundedEdgeRegularSubgraphs.Incidence
public import Mathlib.Data.Matrix.Basic
import BoundedEdgeRegularSubgraphs.MeanDrift
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Degree covariance forms

The entries of the matrix are sums of the Bernoulli variances times products
of endpoint incidence coordinates. The quadratic form is an edge sum.
-/

@[expose] public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The covariance matrix appearing in Appendix A for the available edges. -/
noncomputable def degreeCovariance (A : Finset (Edge α))
    (p : Edge α → Set.Icc (0 : ℝ) 1) : Matrix α α ℝ :=
  fun i j ↦ ∑ e ∈ A, ((p e : ℝ) * (1 - p e)) *
    (edgeIncidence e i : ℝ) * (edgeIncidence e j : ℝ)

private theorem sum_mul_edgeIncidence (t : α → ℝ) (e : Edge α) :
    (∑ i, t i * (edgeIncidence e i : ℝ)) = t e.val.1 + t e.val.2 := by
  classical
  simp only [edgeIncidence, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero,
    mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- The quadratic form of the covariance matrix is the sum over available edges. -/
theorem degreeCovariance_quadratic (A : Finset (Edge α))
    (p : Edge α → Set.Icc (0 : ℝ) 1) (t : α → ℝ) :
    (∑ i, ∑ j, t i * degreeCovariance A p i j * t j) =
      ∑ e ∈ A, ((p e : ℝ) * (1 - p e)) * (t e.val.1 + t e.val.2) ^ 2 := by
  classical
  let v (e : Edge α) := (p e : ℝ) * (1 - p e)
  let x (e : Edge α) (i : α) := t i * (edgeIncidence e i : ℝ)
  calc
    (∑ i, ∑ j, t i * degreeCovariance A p i j * t j) =
        ∑ i, ∑ j, ∑ e ∈ A, v e * (x e i * x e j) := by
      simp only [degreeCovariance, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦
        Finset.sum_congr rfl (fun e _ ↦ ?_)))
      dsimp [v, x]
      ring
    _ = ∑ i, ∑ e ∈ A, ∑ j, v e * (x e i * x e j) :=
      Finset.sum_congr rfl (fun _ _ ↦ Finset.sum_comm)
    _ = ∑ e ∈ A, ∑ i, ∑ j, v e * (x e i * x e j) := Finset.sum_comm
    _ = ∑ e ∈ A, v e * (t e.val.1 + t e.val.2) ^ 2 := by
      refine Finset.sum_congr rfl (fun e _ ↦ ?_)
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      simp [x, sum_mul_edgeIncidence, pow_two]

/-- The covariance form for any available edge set is positive semidefinite. -/
theorem degreeCovariance_quadratic_nonneg (A : Finset (Edge α))
    (p : Edge α → Set.Icc (0 : ℝ) 1) (t : α → ℝ) :
    0 ≤ ∑ i, ∑ j, t i * degreeCovariance A p i j * t j := by
  rw [degreeCovariance_quadratic]
  exact Finset.sum_nonneg fun e _ ↦
    mul_nonneg (mul_nonneg (p e).property.1 (sub_nonneg.mpr (p e).property.2)) (sq_nonneg _)

/-- The exact full-array lower and upper quadratic bounds from Appendix A. -/
theorem degreeCovariance_univ_bounds (p : Edge α → Set.Icc (0 : ℝ) 1)
    (lower : ℝ) (hlower : 0 ≤ lower) (hp : ∀ e, lower ≤ (p e : ℝ) * (1 - p e))
    (t : α → ℝ) :
    lower * (Fintype.card α - 2 : ℝ) * (∑ i, t i ^ 2) ≤
      (∑ i, ∑ j, t i * degreeCovariance Finset.univ p i j * t j) ∧
    (∑ i, ∑ j, t i * degreeCovariance Finset.univ p i j * t j) ≤
      ((Fintype.card α : ℝ) - 1) / 2 * ∑ i, t i ^ 2 := by
  rw [degreeCovariance_quadratic]
  constructor
  · calc
      _ ≤ lower * (∑ e : Edge α, (t e.val.1 + t e.val.2) ^ 2) := by
        rw [sum_edge_squares, mul_add, ← mul_assoc]
        exact le_add_of_nonneg_right (mul_nonneg hlower (sq_nonneg _))
      _ ≤ _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun e _ ↦ mul_le_mul_of_nonneg_right (hp e) (sq_nonneg _))
  · calc
      _ ≤ (1 / 4 : ℝ) * (∑ e : Edge α, (t e.val.1 + t e.val.2) ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun e _ ↦ mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
        nlinarith only [sq_nonneg ((p e : ℝ) - 1 / 2)]
      _ ≤ _ := by
        rw [sum_edge_squares]
        have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := t)
        rw [Finset.card_univ] at h
        linarith only [h]

end BoundedEdgeRegularSubgraphs
