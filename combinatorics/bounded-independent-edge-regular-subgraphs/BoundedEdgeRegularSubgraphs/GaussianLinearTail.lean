module

public import BoundedEdgeRegularSubgraphs.GaussianLinearMoments
public import BoundedEdgeRegularSubgraphs.FourierStrongConvexity
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic

/-!
# Tail probabilities of the Gaussian linear image
-/

public section

open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators NNReal

namespace BoundedEdgeRegularSubgraphs

/-- The tail of the absolute value of a Gaussian linear form is bounded
using any positive upper bound on its variance. -/
theorem probability_abs_dotProduct_gt_le {n : ℕ} (v : Fin n → ℝ)
    {D r : ℝ} (hD : 0 < D) (hv : (∑ i, v i ^ 2) ≤ D) (hr : 0 ≤ r) :
    (standardGaussianProduct n).real {x | r < |v ⬝ᵥ x|} ≤
      2 * Real.exp (-r ^ 2 / (2 * D)) := by
  let γ := standardGaussianProduct n
  let X (x : Fin n → ℝ) := v ⬝ᵥ x
  let s := r / D
  let V : ℝ≥0 := ⟨∑ i, v i ^ 2, Finset.sum_nonneg (fun i _ ↦ sq_nonneg (v i))⟩
  have hX : Measurable X := by
    unfold X dotProduct
    exact Finset.measurable_sum _ (fun i _ ↦ measurable_const.mul (measurable_pi_apply i))
  have hLaw : HasLaw X (gaussianReal 0 V) γ :=
    ⟨hX.aemeasurable, map_standardGaussianProduct_dotProduct v⟩
  have hInt (t : ℝ) : Integrable (fun x ↦ Real.exp (t * X x)) γ :=
    hLaw.integrable_comp (integrable_exp_mul_gaussianReal t)
  have hs : 0 ≤ s := div_nonneg hr hD.le
  have hExp : -s * r + ↑V * s ^ 2 / 2 ≤ -r ^ 2 / (2 * D) := by
    have h := mul_le_mul_of_nonneg_right hv (sq_nonneg s)
    change (V : ℝ) * s ^ 2 ≤ D * s ^ 2 at h
    have he : -s * r + D * s ^ 2 / 2 = -r ^ 2 / (2 * D) := by
      dsimp only [s]
      field_simp
      ring
    rw [← he]
    linarith only [h]
  have h₁ : γ.real {x | r ≤ X x} ≤ Real.exp (-r ^ 2 / (2 * D)) := by
    have h := measure_ge_le_exp_cgf (X := X) r hs (hInt s)
    rw [cgf_gaussianReal hLaw, zero_mul, zero_add] at h
    exact h.trans (Real.exp_le_exp.mpr hExp)
  have h₂ : γ.real {x | X x ≤ -r} ≤ Real.exp (-r ^ 2 / (2 * D)) := by
    have h := measure_le_le_exp_cgf (X := X) (-r) (neg_nonpos.mpr hs) (hInt (-s))
    rw [cgf_gaussianReal hLaw, zero_mul, zero_add, neg_neg, neg_sq] at h
    refine h.trans (Real.exp_le_exp.mpr ?_)
    linarith only [hExp]
  have hsub : {x | r < |X x|} ⊆ {x | r ≤ X x} ∪ {x | X x ≤ -r} := by
    intro x hx
    have hx' : ¬ (-r ≤ X x ∧ X x ≤ r) := fun h ↦ (not_le_of_gt hx) (abs_le.mpr h)
    exact (not_and_or.mp hx').elim (fun h ↦ Or.inr (lt_of_not_ge h).le)
      (fun h ↦ Or.inl (lt_of_not_ge h).le)
  calc
    _ ≤ γ.real ({x | r ≤ X x} ∪ {x | X x ≤ -r}) := measureReal_mono hsub
    _ ≤ γ.real {x | r ≤ X x} + γ.real {x | X x ≤ -r} := measureReal_union_le _ _
    _ ≤ _ := by linarith only [h₁, h₂]

/-- A union bound for the Gaussian mass outside the shrinking real box. -/
theorem probability_gaussian_mulVec_outside_box_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    {D r : ℝ} (hD : 0 < D) (hB : ∀ i, (∑ j, (B i j) ^ 2) ≤ D) (hr : 0 ≤ r) :
    (standardGaussianProduct n).real {x | B *ᵥ x ∉ realPhaseBox (α := Fin n) r} ≤
      2 * n * Real.exp (-r ^ 2 / (2 * D)) := by
  let T (i : Fin n) := {x : Fin n → ℝ | r < |(B *ᵥ x) i|}
  have he : {x | B *ᵥ x ∉ realPhaseBox (α := Fin n) r} = ⋃ i, T i := by
    ext x
    simp only [realPhaseBox, mem_setOf_eq, mem_iUnion, T, not_forall, not_le]
  rw [he]
  calc
    _ ≤ ∑ i, (standardGaussianProduct n).real (T i) := measureReal_iUnion_fintype_le T
    _ ≤ ∑ _ : Fin n, 2 * Real.exp (-r ^ 2 / (2 * D)) :=
      Finset.sum_le_sum (fun i _ ↦ probability_abs_dotProduct_gt_le (B i) hD (hB i) hr)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end BoundedEdgeRegularSubgraphs
