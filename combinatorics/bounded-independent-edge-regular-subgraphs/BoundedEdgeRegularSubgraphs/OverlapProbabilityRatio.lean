module

public import BoundedEdgeRegularSubgraphs.OverlapConditioning
public import BoundedEdgeRegularSubgraphs.OverlapDeterminant
import Mathlib.Tactic

/-!
# Combining the upper and lower atom bounds in the conditional comparison
-/

public section

open MeasureTheory
open scoped BigOperators Matrix

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

private theorem covariance_det_pos_of_isUnit (A : Finset (Edge α))
    (p : Edge α → Set.Icc (0 : ℝ) 1) (h : IsUnit (degreeCovariance A p).det) :
    0 < (degreeCovariance A p).det := by
  classical
  have hsymm : (degreeCovariance A p).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, degreeCovariance]
    exact Finset.sum_congr rfl (fun e _ ↦ by ring)
  have hPSD : (degreeCovariance A p).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hsymm
    intro x
    rw [star_trivial, Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
    exact degreeCovariance_quadratic_nonneg A p x
  exact lt_of_le_of_ne' hPSD.det_nonneg (isUnit_iff_ne_zero.mp h)

private theorem covariance_det_univ_pos (p : Edge α → Set.Icc (0 : ℝ) 1)
    (hn : 3 ≤ Fintype.card α) (lower : ℝ) (hlower : 0 < lower)
    (hp : ∀ e, lower ≤ (p e : ℝ) * (1 - p e)) : 0 < (degreeCovariance Finset.univ p).det := by
  classical
  apply covariance_det_pos_of_isUnit
  have hn' : (3 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  have hc : 0 < lower * ((Fintype.card α : ℝ) - 2) := mul_pos hlower (by linarith)
  apply (inverse_mulVec_sq_le_of_quadratic _ hc ?_).1
  intro x
  rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
  exact (degreeCovariance_univ_bounds p lower hlower.le hp x).1

/-- The finite deduction in Corollary C.2 from a lower bound on the full
atom and an upper bound on the residual atom. -/
theorem probability_conditional_ratio_le_of_atom_bounds (S : Finset α)
    (hm : 3 ≤ ((Finset.univ : Finset α) \ S).card)
    (p : Edge α → Set.Icc (0 : ℝ) 1) (lower : ℝ) (hlower : 0 < lower)
    (hp : ∀ e, lower ≤ (p e : ℝ) * (1 - p e)) (h : Edge α → ℝ) (d : α → ℤ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hpos : 0 < (graphLaw p).real (overlapAssignmentEvent S h))
    (hfull : a / Real.sqrt (degreeCovariance Finset.univ p).det ≤
      (graphLaw p).real (degreeAtom Finset.univ d))
    (hres : (graphLaw p).real
      (degreeAtom (edgesOutsideOverlap S) (d - degreeVector (edgesInside S) h)) ≤
        b / Real.sqrt (degreeCovariance (edgesOutsideOverlap S) p).det) :
    let c : ℝ := lower * ((((Finset.univ : Finset α) \ S).card : ℝ) ^ 2 / (3 * Fintype.card α))
    (((graphLaw p).real (degreeAtom Finset.univ d ∩ overlapAssignmentEvent S h) /
      (graphLaw p).real (overlapAssignmentEvent S h)) /
      (graphLaw p).real (degreeAtom Finset.univ d)) ≤
        (b / a) * Real.exp ((S.card : ℝ) * ((S.card : ℝ) - 1) / (8 * c)) := by
  classical
  intro c
  let U := (degreeCovariance Finset.univ p).det
  let V := (degreeCovariance (edgesOutsideOverlap S) p).det
  let g := (S.card : ℝ) * ((S.card : ℝ) - 1) / (8 * c)
  have hn : 3 ≤ Fintype.card α := hm.trans (Finset.card_le_univ _)
  have hU : 0 < U := covariance_det_univ_pos p hn lower hlower hp
  have hV : 0 < V := covariance_det_pos_of_isUnit _ p
    (degreeCovariance_outside_overlap_inverse_bounds S hm p lower hlower hp).1
  have hUs : 0 < Real.sqrt U := Real.sqrt_pos.mpr hU
  have hVs : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hcompare : Real.sqrt U ≤ Real.sqrt V * Real.exp g := by
    have hdet := degreeCovariance_det_overlap_le S hm p lower hlower hp
    dsimp only at hdet
    have hr : (Real.sqrt V * Real.exp g) ^ 2 =
        V * Real.exp ((S.card : ℝ) * ((S.card : ℝ) - 1) / (4 * c)) := by
      rw [mul_pow, Real.sq_sqrt hV.le, pow_two (Real.exp g), ← Real.exp_add]
      rw [show g + g = (S.card : ℝ) * ((S.card : ℝ) - 1) / (4 * c) by dsimp [g]; ring]
    apply (sq_le_sq₀ hUs.le (by positivity)).mp
    rw [Real.sq_sqrt hU.le, hr]
    exact hdet
  have hratio : Real.sqrt U / Real.sqrt V ≤ Real.exp g := by
    apply (div_le_iff₀ hVs).mpr
    rw [mul_comm]
    exact hcompare
  rw [probability_degreeAtom_given_overlap_eq p S h d hpos]
  calc
    _ ≤ (b / Real.sqrt V) / (a / Real.sqrt U) := by
      apply div_le_div₀ (div_nonneg hb hVs.le) hres (div_pos ha hUs) hfull
    _ = (b / a) * (Real.sqrt U / Real.sqrt V) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hratio (div_nonneg hb ha.le)

end BoundedEdgeRegularSubgraphs
