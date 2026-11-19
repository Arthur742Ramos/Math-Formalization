module

public import BoundedEdgeRegularSubgraphs.DiagonalLargeCells
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

/-!
# The quadratic diagonal bound for smooth symmetric kernels
-/

public section

open Set

namespace BoundedEdgeRegularSubgraphs

/-- A symmetric kernel with a twice continuously differentiable extension
to an open neighbourhood of the product cube satisfies the diagonal condition
in Remark 6.5. -/
theorem exists_cubeDiagonalQuadratic_of_contDiff {d : ℕ}
    (W : (Fin d → Icc (0 : ℝ) 1) → (Fin d → Icc (0 : ℝ) 1) → Icc (0 : ℝ) 1)
    (hSymm : ∀ x y, W x y = W y x)
    (w : (Fin d → ℝ) × (Fin d → ℝ) → ℝ)
    (hExt : ∀ x y, w ((fun i ↦ (x i : ℝ)), (fun i ↦ (y i : ℝ))) = (W x y : ℝ))
    (U : Set ((Fin d → ℝ) × (Fin d → ℝ))) (hU : IsOpen U)
    (hSubset : (Icc (0 : Fin d → ℝ) 1) ×ˢ (Icc (0 : Fin d → ℝ) 1) ⊆ U)
    (hC : ContDiffOn ℝ 2 w U) :
    ∃ B : ℝ, 0 ≤ B ∧ CubeDiagonalQuadratic B W := by
  let E := Fin d → ℝ
  let I : Set E := Icc 0 1
  let K := I ×ˢ I
  let D := fderiv ℝ w
  have hI : Convex ℝ I := convex_Icc _ _
  have hK : Convex ℝ K := hI.prod hI
  have hcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hD : ContDiffOn ℝ 1 D U := hC.fderiv_of_isOpen hU (by norm_num)
  have hDD : ContinuousOn (fderiv ℝ D) U := by
    exact ((contDiffOn_succ_iff_fderiv_of_isOpen hU).mp
      (show ContDiffOn ℝ (0 + 1) D U by simpa only [zero_add] using hD)).2.2.continuousOn
  have hNorm : ContinuousOn (fun z : E × E ↦ ‖fderiv ℝ D z‖) K := by
    have hcont : Continuous (fun A : (E × E) →L[ℝ] (E × E →L[ℝ] ℝ) ↦ ‖A‖) :=
      @continuous_norm ((E × E) →L[ℝ] (E × E →L[ℝ] ℝ)) inferInstance
    exact hcont.comp_continuousOn (hDD.mono hSubset)
  obtain ⟨A, hA⟩ := hcompact.bddAbove_image hNorm
  let B := max 0 A
  have hB : 0 ≤ B := le_max_left _ _
  have hDerivativeDifference (z z' : E × E) (hz : z ∈ K) (hz' : z' ∈ K) :
      ‖D z' - D z‖ ≤ B * ‖z' - z‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun x hx ↦ (hD.differentiableOn (by norm_num) x (hSubset hx)).differentiableAt (hU.mem_nhds (hSubset hx)))
      (fun x hx ↦ (hA (Set.mem_image_of_mem _ hx)).trans (le_max_right _ _)) hK hz hz'
  refine ⟨B, hB, ?_⟩
  intro x y ε hε hxy
  let a : E := fun i ↦ (x i : ℝ)
  let b : E := fun i ↦ (y i : ℝ)
  have ha : a ∈ I := ⟨fun i ↦ (x i).property.1, fun i ↦ (x i).property.2⟩
  have hb : b ∈ I := ⟨fun i ↦ (y i).property.1, fun i ↦ (y i).property.2⟩
  have hNorm : ‖b - a‖ ≤ ε := by
    apply (pi_norm_le_iff_of_nonneg hε).mpr
    intro i
    change ‖(y i : ℝ) - (x i : ℝ)‖ ≤ ε
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact hxy i
  let F (z : E) := w (z, b) - w (z, a)
  let i₁ := ContinuousLinearMap.inl ℝ E E
  have hF (z : E) (hz : z ∈ I) :
      HasFDerivAt F ((D (z, b) - D (z, a)).comp i₁) z := by
    have pairDerivative (c : E) :
        HasFDerivAt (fun z' : E ↦ (z', c)) i₁ z := by
      have h := (hasFDerivAt_id (𝕜 := ℝ) z).prodMk (hasFDerivAt_const (𝕜 := ℝ) c z)
      have he : (ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] E) = i₁ := by
        apply ContinuousLinearMap.ext
        intro v
        simp [i₁]
      rw [he] at h
      exact h
    have h₁ (c : E) (hc : c ∈ I) :
        HasFDerivAt w (D (z, c)) (z, c) :=
      ((hC.differentiableOn (by norm_num) (z, c) (hSubset ⟨hz, hc⟩)).differentiableAt
        (hU.mem_nhds (hSubset ⟨hz, hc⟩))).hasFDerivAt
    have h := ((h₁ b hb).comp z (pairDerivative b)).sub ((h₁ a ha).comp z (pairDerivative a))
    have he : (D (z, b) - D (z, a)).comp i₁ = (D (z, b)).comp i₁ - (D (z, a)).comp i₁ := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply]
    rw [he]
    exact h
  have hbnd (z : E) (hz : z ∈ I) : ‖fderiv ℝ F z‖ ≤ B * ‖b - a‖ := by
    rw [(hF z hz).fderiv]
    have hcl : ‖D (z, b) - D (z, a)‖ ≤ B * ‖b - a‖ := by
      have h := hDerivativeDifference (z, a) (z, b) ⟨hz, ha⟩ ⟨hz, hb⟩
      simpa only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero,
        max_eq_right (norm_nonneg (b - a))] using h
    exact ((D (z, b) - D (z, a)).opNorm_comp_le i₁).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_inl_le_one _ _ _)).trans hcl)
  have hDifference := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz ↦ (hF z hz).differentiableAt) hbnd hI ha hb
  change ‖(w (b, b) - w (b, a)) - (w (a, b) - w (a, a))‖ ≤ _ at hDifference
  rw [hExt y y, hExt y x, hExt x y, hExt x x, hSymm y x, Real.norm_eq_abs] at hDifference
  have hEq : (W x x : ℝ) + (W y y : ℝ) - 2 * (W x y : ℝ) =
      ((W y y : ℝ) - (W x y : ℝ)) - ((W x y : ℝ) - (W x x : ℝ)) := by ring
  rw [hEq]
  exact hDifference.trans (by
    rw [mul_assoc, ← pow_two]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hNorm 2) hB)

end BoundedEdgeRegularSubgraphs
