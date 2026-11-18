module

public import BoundedEdgeRegularSubgraphs.CovarianceSup
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-!
# A quantitative fixed point for the centring equation
-/

public section

open scoped Matrix

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- An invertible linear part and a small remainder give a zero of the
perturbed equation on the same closed maximum-norm ball. -/
theorem exists_perturbation_zero (A : Matrix α α ℝ) (hA : IsUnit A.det)
    (r : α → ℝ) (R : (α → ℝ) → α → ℝ) (hR₀ : R 0 = 0) {b L M : ℝ}
    (hb : 0 ≤ b) (hL : 0 ≤ L)
    (hAinv : ∀ x : α → ℝ, ‖A⁻¹ *ᵥ x‖ ≤ L * ‖x‖)
    (hR : ∀ x y : α → ℝ, ‖x‖ ≤ b → ‖y‖ ≤ b → ‖R x - R y‖ ≤ M * ‖x - y‖)
    (hLM : L * M ≤ 1 / 2) (hr : L * ‖r‖ ≤ b / 2) :
    ∃ x : α → ℝ, ‖x‖ ≤ b ∧ r + A *ᵥ x + R x = 0 := by
  let E := α → ℝ
  let S := Metric.closedBall (0 : E) b
  let F (x : E) : E := -(A⁻¹ *ᵥ (r + R x))
  have hS : ∀ x : E, x ∈ S ↔ ‖x‖ ≤ b := by
    intro x
    simp [S]
  have hdist (x y : E) (hx : x ∈ S) (hy : y ∈ S) :
      ‖F x - F y‖ ≤ (1 / 2 : ℝ) * ‖x - y‖ := by
    have he : F x - F y = -(A⁻¹ *ᵥ (R x - R y)) := by
      dsimp only [F]
      rw [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_add]
      abel
    rw [he, norm_neg]
    calc
      _ ≤ L * ‖R x - R y‖ := hAinv _
      _ ≤ L * (M * ‖x - y‖) := mul_le_mul_of_nonneg_left
        (hR x y ((hS x).mp hx) ((hS y).mp hy)) hL
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hLM (norm_nonneg _)
  have hF₀ : ‖F 0‖ ≤ b / 2 := by
    dsimp only [F]
    rw [hR₀, add_zero, norm_neg]
    exact (hAinv r).trans hr
  have hzero : 0 ∈ S := (hS 0).mpr (by simpa using hb)
  have hmap : Set.MapsTo F S S := by
    intro x hx
    apply (hS (F x)).mpr
    have htri : ‖F x‖ ≤ ‖F x - F 0‖ + ‖F 0‖ := by
      simpa only [sub_add_cancel] using norm_add_le (F x - F 0) (F 0)
    have hd := hdist x 0 hx hzero
    rw [sub_zero] at hd
    linarith only [htri, hd, (hS x).mp hx, hF₀]
  have hcontract : ContractingWith (1 / 2) (hmap.restrict F S S) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (F x.val) (F y.val) ≤ (1 / 2 : ℝ) * dist x.val y.val
    rw [dist_eq_norm, dist_eq_norm]
    exact hdist x.val y.val x.property y.property
  obtain ⟨x, hx, hF, _, _⟩ := hcontract.exists_fixedPoint' Metric.isClosed_closedBall.isComplete
    hmap hzero (edist_ne_top _ _)
  refine ⟨x, (hS x).mp hx, ?_⟩
  have he : x = -(A⁻¹ *ᵥ (r + R x)) := hF.symm
  have hxA : A *ᵥ x = -(r + R x) := by
    calc
      _ = A *ᵥ (-(A⁻¹ *ᵥ (r + R x))) := congrArg (fun y : E ↦ A *ᵥ y) he
      _ = _ := by
        rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec]
  rw [hxA]
  abel

end BoundedEdgeRegularSubgraphs
