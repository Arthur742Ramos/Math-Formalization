module

public import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Tensorization of variance
-/

public section

open MeasureTheory ProbabilityTheory

namespace BoundedEdgeRegularSubgraphs

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

private theorem memLp_integral_product_right (F : X × Y → ℝ) (hF : MemLp F 2 (μ.prod ν)) :
    MemLp (fun x ↦ ∫ y, F (x, y) ∂ν) 2 μ := by
  let f (x : X) := ∫ y, F (x, y) ∂ν
  have hFi : Integrable F (μ.prod ν) := hF.integrable (by simp)
  have hF₂ := hF.integrable_sq
  have hf : Integrable f μ := hFi.integral_prod_left
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
  refine hF₂.integral_prod_left.mono' ((hf.aestronglyMeasurable.pow 2)) ?_
  filter_upwards [hFi.prod_right_ae, hF₂.prod_right_ae] with x hx hx₂
  have h : MemLp (fun y ↦ F (x, y)) 2 ν :=
    (memLp_two_iff_integrable_sq hx.aestronglyMeasurable).2 hx₂
  have hv : 0 ≤ Var[(fun y ↦ F (x, y)); ν] := variance_nonneg _ _
  rw [variance_eq_sub h] at hv
  change ‖f x ^ 2‖ ≤ ∫ y, F (x, y) ^ 2 ∂ν
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sub_nonneg.mp hv

/-- The variance of a function of two independent coordinates is at most
the sum of the expected variances when one coordinate is fixed. -/
theorem variance_prod_le_integral_slice_variances (F : X × Y → ℝ)
    (hF : MemLp F 2 (μ.prod ν)) :
    Var[F; μ.prod ν] ≤
      (∫ x, Var[(fun y ↦ F (x, y)); ν] ∂μ) +
      (∫ y, Var[(fun x ↦ F (x, y)); μ] ∂ν) := by
  let A (x : X) := ∫ y, F (x, y) ∂ν
  let B (y : Y) := ∫ x, F (x, y) ∂μ
  let P := μ.prod ν
  let a (z : X × Y) := A z.1
  let b (z : X × Y) := B z.2
  let m := ∫ z, F z ∂P
  let M := ∫ z, F z ^ 2 ∂P
  let S := ∫ x, A x ^ 2 ∂μ
  let T := ∫ y, B y ^ 2 ∂ν
  have hFi : Integrable F P := hF.integrable (by simp)
  have hF₂ : Integrable (fun z ↦ F z ^ 2) P := hF.integrable_sq
  have hA : MemLp A 2 μ := memLp_integral_product_right F hF
  have hB : MemLp B 2 ν := memLp_integral_product_right (F ∘ Prod.swap)
    (hF.comp_measurePreserving Measure.measurePreserving_swap)
  have hμA : (∫ x, A x ∂μ) = m := (integral_prod F hFi).symm
  have hνB : (∫ y, B y ∂ν) = m := (integral_prod_symm F hFi).symm
  have ha : MemLp a 2 P := hA.comp_measurePreserving measurePreserving_fst
  have hb : MemLp b 2 P := hB.comp_measurePreserving measurePreserving_snd
  have ha₁ : (∫ z, a z ∂P) = m := by
    rw [integral_prod _ (ha.integrable (by simp))]
    simpa only [a, integral_const, probReal_univ, one_smul] using hμA
  have hb₁ : (∫ z, b z ∂P) = m := by
    rw [integral_prod_symm _ (hb.integrable (by simp))]
    simpa only [b, integral_const, probReal_univ, one_smul] using hνB
  have ha₂ : (∫ z, a z ^ 2 ∂P) = S := by
    rw [integral_prod _ ha.integrable_sq]
    simp only [a, integral_const, probReal_univ, one_smul, S]
  have hb₂ : (∫ z, b z ^ 2 ∂P) = T := by
    rw [integral_prod_symm _ hb.integrable_sq]
    simp only [b, integral_const, probReal_univ, one_smul, T]
  have hmulA : Integrable (fun z ↦ a z * F z) P := ha.integrable_mul hF
  have hmulB : Integrable (fun z ↦ b z * F z) P := hb.integrable_mul hF
  have hmulAB : Integrable (fun z ↦ a z * b z) P := ha.integrable_mul hb
  have hSA : (∫ z, a z * F z ∂P) = S := by
    rw [integral_prod _ hmulA]
    simp_rw [a, integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ (pow_two (A x)).symm)
  have hTB : (∫ z, b z * F z ∂P) = T := by
    rw [integral_prod_symm _ hmulB]
    simp_rw [b, integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y ↦ (pow_two (B y)).symm)
  have hAB : (∫ z, a z * b z ∂P) = m ^ 2 := by
    change (∫ z, A z.1 * B z.2 ∂P) = _
    rw [integral_prod_mul, hμA, hνB, pow_two]
  have hS : (∫ x, Var[(fun y ↦ F (x, y)); ν] ∂μ) = M - S := by
    have he : (fun x ↦ Var[(fun y ↦ F (x, y)); ν]) =ᵐ[μ]
        fun x ↦ (∫ y, F (x, y) ^ 2 ∂ν) - A x ^ 2 := by
      filter_upwards [hFi.prod_right_ae, hF₂.prod_right_ae] with x hx hx₂
      exact variance_eq_sub ((memLp_two_iff_integrable_sq hx.aestronglyMeasurable).2 hx₂)
    rw [integral_congr_ae he, integral_sub hF₂.integral_prod_left hA.integrable_sq,
      ← integral_prod _ hF₂]
  have hT : (∫ y, Var[(fun x ↦ F (x, y)); μ] ∂ν) = M - T := by
    have he : (fun y ↦ Var[(fun x ↦ F (x, y)); μ]) =ᵐ[ν]
        fun y ↦ (∫ x, F (x, y) ^ 2 ∂μ) - B y ^ 2 := by
      filter_upwards [hFi.prod_left_ae, hF₂.prod_left_ae] with y hy hy₂
      exact variance_eq_sub ((memLp_two_iff_integrable_sq hy.aestronglyMeasurable).2 hy₂)
    rw [integral_congr_ae he, integral_sub hF₂.integral_prod_right hB.integrable_sq,
      ← integral_prod_symm _ hF₂]
  let g (z : X × Y) := F z - a z - b z
  have hg : MemLp g 2 P := (hF.sub ha).sub hb
  have hmg : (∫ z, g z ∂P) = -m := by
    have hia : Integrable a P := ha.integrable (by simp)
    have hib : Integrable b P := hb.integrable (by simp)
    have hf_sub_a : Integrable (fun z ↦ F z - a z) P := hFi.sub hia
    change (∫ z, F z - a z - b z ∂P) = _
    rw [integral_sub hf_sub_a hib, integral_sub hFi hia, ha₁, hb₁]
    change m - m - m = -m
    ring
  have hEg : (∫ z, g z ^ 2 ∂P) = M - S - T + 2 * m ^ 2 := by
    have hpoint (z : X × Y) : g z ^ 2 = F z ^ 2 + a z ^ 2 + b z ^ 2 -
        2 * (a z * F z + b z * F z - a z * b z) := by dsimp only [g]; ring
    have hiA : Integrable (fun z ↦ a z ^ 2) P := ha.integrable_sq
    have hiB : Integrable (fun z ↦ b z ^ 2) P := hb.integrable_sq
    have hiL₁ : Integrable (fun z ↦ F z ^ 2 + a z ^ 2) P := hF₂.add hiA
    have hiL : Integrable (fun z ↦ F z ^ 2 + a z ^ 2 + b z ^ 2) P := hiL₁.add hiB
    have hiR₁ : Integrable (fun z ↦ a z * F z + b z * F z) P := hmulA.add hmulB
    have hiR : Integrable (fun z ↦ a z * F z + b z * F z - a z * b z) P :=
      hiR₁.sub hmulAB
    simp_rw [hpoint]
    rw [integral_sub hiL (hiR.const_mul (2 : ℝ)), integral_const_mul,
      integral_add hiL₁ hiB, integral_add hF₂ hiA,
      integral_sub hiR₁ hmulAB, integral_add hmulA hmulB,
      ha₂, hb₂, hSA, hTB, hAB]
    change M + S + T - 2 * (S + T - m ^ 2) = _
    ring
  have hx : 0 ≤ Var[g; P] := variance_nonneg _ _
  rw [variance_eq_sub hg] at hx
  change 0 ≤ (∫ z, g z ^ 2 ∂P) - (∫ z, g z ∂P) ^ 2 at hx
  rw [hEg, hmg, neg_sq] at hx
  rw [variance_eq_sub hF, hS, hT]
  change M - m ^ 2 ≤ (M - S) + (M - T)
  linarith only [hx]

end BoundedEdgeRegularSubgraphs
