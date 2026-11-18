module

public import BoundedEdgeRegularSubgraphs.CentringFixedPoint
public import BoundedEdgeRegularSubgraphs.TiltDerivative
import BoundedEdgeRegularSubgraphs.RegularAtomUpper
import Mathlib.Tactic

/-!
# Centring the expected degrees of the full independent-edge array
-/

public section

open scoped BigOperators Matrix

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

private theorem degreeSum_eq_incidence (w : Edge α → ℝ) (i : α) :
    degreeSum w i = ∑ e, (edgeIncidence e i : ℝ) * w e := by
  apply Finset.sum_congr rfl
  intro e _
  have h := ne_of_lt e.property
  by_cases h₁ : i = e.val.1
  · subst i
    simp [edgeIncidence, h]
  · by_cases h₂ : i = e.val.2
    · subst i
      simp [edgeIncidence, h.symm]
    · simp [edgeIncidence, h₁, h₂]

private theorem degreeCovariance_mulVec (q : Edge α → Set.Icc (0 : ℝ) 1)
    (θ : α → ℝ) :
    degreeCovariance Finset.univ q *ᵥ θ =
      degreeSum (fun e ↦ (q e : ℝ) * (1 - q e) * (θ e.val.1 + θ e.val.2)) := by
  classical
  funext i
  rw [degreeSum_eq_incidence]
  change (∑ j, degreeCovariance Finset.univ q i j * θ j) = _
  simp only [degreeCovariance, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have hs : (∑ j : α, (edgeIncidence e j : ℝ) * θ j) = θ e.val.1 + θ e.val.2 := by
    simp only [edgeIncidence, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero,
      add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  calc
    _ = ((q e : ℝ) * (1 - q e) * (edgeIncidence e i : ℝ)) *
        ∑ j, (edgeIncidence e j : ℝ) * θ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ ↦ by ring)
    _ = _ := by rw [hs]; ring

private noncomputable def degreeTiltRemainder (q : Edge α → Set.Icc (0 : ℝ) 1) (θ : α → ℝ) :
    α → ℝ :=
  degreeSum (fun e ↦ tiltRemainder (q e) (θ e.val.1 + θ e.val.2))

private theorem degreeTiltRemainder_zero (q : Edge α → Set.Icc (0 : ℝ) 1) :
    degreeTiltRemainder q 0 = 0 := by
  funext i
  simp [degreeTiltRemainder, degreeSum]

private theorem degreeTilt_eq (q : Edge α → Set.Icc (0 : ℝ) 1) (θ : α → ℝ) :
    degreeSum (fun e ↦ (vertexTilt q θ e : ℝ)) =
      degreeSum (fun e ↦ (q e : ℝ)) + degreeCovariance Finset.univ q *ᵥ θ +
        degreeTiltRemainder q θ := by
  rw [degreeCovariance_mulVec]
  funext i
  simp only [degreeTiltRemainder, Pi.add_apply, degreeSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs
  · dsimp [vertexTilt, tiltRemainder]
    ring
  · ring

omit [LinearOrder α] in
private theorem abs_coord_le_norm (x : α → ℝ) (i : α) : |x i| ≤ ‖x‖ := by
  rw [← Real.norm_eq_abs]
  exact norm_le_pi_norm x i

private theorem degreeTiltRemainder_norm_le (q : Edge α → Set.Icc (0 : ℝ) 1)
    {b : ℝ} (hb : 0 ≤ b) (θ φ : α → ℝ) (hθ : ‖θ‖ ≤ b) (hφ : ‖φ‖ ≤ b) :
    ‖degreeTiltRemainder q θ - degreeTiltRemainder q φ‖ ≤
      ((Fintype.card α : ℝ) * b) * ‖θ - φ‖ := by
  let M := b * ‖θ - φ‖
  have hM : 0 ≤ M := mul_nonneg hb (norm_nonneg _)
  have hEdge : ∀ e : Edge α,
      |tiltRemainder (q e) (θ e.val.1 + θ e.val.2) -
        tiltRemainder (q e) (φ e.val.1 + φ e.val.2)| ≤ M := by
    intro e
    have hbound (x : α → ℝ) (hx : ‖x‖ ≤ b) :
        |x e.val.1 + x e.val.2| ≤ 2 * b := by
      exact (abs_add_le _ _).trans (by
        linarith only [(abs_coord_le_norm x e.val.1).trans hx, (abs_coord_le_norm x e.val.2).trans hx])
    have hdiff : |θ e.val.1 + θ e.val.2 - (φ e.val.1 + φ e.val.2)| ≤ 2 * ‖θ - φ‖ := by
      rw [show θ e.val.1 + θ e.val.2 - (φ e.val.1 + φ e.val.2) =
        (θ - φ) e.val.1 + (θ - φ) e.val.2 by simp only [Pi.sub_apply]; ring]
      exact (abs_add_le _ _).trans (by
        linarith only [abs_coord_le_norm (θ - φ) e.val.1, abs_coord_le_norm (θ - φ) e.val.2])
    refine (abs_tiltRemainder_sub_le (q e) (hbound θ hθ) (hbound φ hφ)).trans ?_
    calc
      _ ≤ (2 * b / 4) * (2 * ‖θ - φ‖) := mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = _ := by dsimp [M]; ring
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  let w₁ (e : Edge α) := tiltRemainder (q e) (θ e.val.1 + θ e.val.2)
  let w₂ (e : Edge α) := tiltRemainder (q e) (φ e.val.1 + φ e.val.2)
  let ind (e : Edge α) : Prop := i = e.val.1 ∨ i = e.val.2
  classical
  change ‖(∑ e, if ind e then w₁ e else 0) - (∑ e, if ind e then w₂ e else 0)‖ ≤ _
  rw [Real.norm_eq_abs, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ e, |(if ind e then w₁ e else 0) - (if ind e then w₂ e else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, if ind e then M else 0 := by
      apply Finset.sum_le_sum
      intro e _
      split_ifs with he
      · exact hEdge e
      · simp
    _ = degreeSum (fun _ ↦ (1 : ℝ)) i * M := by
      simp only [degreeSum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      change (if ind e then M else 0) = (if ind e then 1 else 0) * M
      split_ifs <;> simp
    _ ≤ (Fintype.card α : ℝ) * M := by
      apply mul_le_mul_of_nonneg_right _ hM
      exact (degreeSum_probability_bounds (fun _ ↦ (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1)) i).2.trans
        (sub_le_self _ (by norm_num))
    _ = _ := by dsimp [M]; ring

/-- A vertex tilt centres any target sufficiently close to the mean in
maximum norm, with the maximum-norm bound of Lemma 2.1. -/
theorem exists_centered_vertexTilt (ξ : ℝ) (hξ : 0 < ξ) (hξ' : ξ < 1 / 2) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ {α : Type*} [Fintype α] [LinearOrder α], 3 ≤ Fintype.card α →
      ∀ (q : Edge α → Set.Icc (0 : ℝ) 1) (d : α → ℝ),
      (∀ e, ξ ≤ (q e : ℝ) ∧ (q e : ℝ) ≤ 1 - ξ) →
      ‖degreeSum (fun e ↦ (q e : ℝ)) - d‖ ≤ ε * Fintype.card α →
      ∃ θ : α → ℝ, degreeSum (fun e ↦ (vertexTilt q θ e : ℝ)) = d ∧
        ‖θ‖ ≤ 1 ∧ ‖θ‖ ≤ C * ‖degreeSum (fun e ↦ (q e : ℝ)) - d‖ / Fintype.card α := by
  have hlow : 0 < ξ * (1 - ξ) := mul_pos hξ (by linarith)
  obtain ⟨C, hC, hmatrix⟩ := degreeCovariance_full_inverse_rows _ hlow
  let ε := min (1 / (2 * C)) (1 / (4 * C ^ 2))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  refine ⟨ε, 2 * C, hε, by positivity, ?_⟩
  intro β _ _ hn q d hq hd
  let k : ℝ := Fintype.card β
  let A := degreeCovariance Finset.univ q
  let r := degreeSum (fun e ↦ (q e : ℝ)) - d
  let b := 2 * C * ‖r‖ / k
  have hk : 0 < k := by dsimp only [k]; exact_mod_cast (show 0 < Fintype.card β by omega)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hsmall : ‖r‖ / k ≤ ε := (div_le_iff₀ hk).mpr hd
  have hb' : b = 2 * C * (‖r‖ / k) := by dsimp only [b]; rw [mul_div_assoc]
  have hb₁ : b ≤ 1 := by
    rw [hb']
    calc
      _ ≤ 2 * C * (1 / (2 * C)) :=
        mul_le_mul_of_nonneg_left (hsmall.trans (min_le_left _ _)) (by positivity)
      _ = 1 := by field_simp
  have he : (C / k) * (k * b) ≤ 1 / 2 := by
    have hc : (C / k) * (k * b) = C * b := by field_simp
    rw [hc, hb', ← mul_assoc]
    calc
      _ ≤ (C * (2 * C)) * (1 / (4 * C ^ 2)) :=
        mul_le_mul_of_nonneg_left (hsmall.trans (min_le_right _ _)) (by positivity)
      _ = _ := by field_simp; norm_num
  have hv (e : Edge β) : ξ * (1 - ξ) ≤ (q e : ℝ) * (1 - q e) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr (hq e).1) (sub_nonneg.mpr (hq e).2)]
  obtain ⟨hA, hrows⟩ := hmatrix hn q hv
  obtain ⟨θ, hθ, hroot⟩ := exists_perturbation_zero A hA r (degreeTiltRemainder q)
    (degreeTiltRemainder_zero q) hb (div_nonneg hC.le hk.le)
    (matrix_mulVec_norm_le_of_row_sum A⁻¹ (div_nonneg hC.le hk.le) hrows)
    (fun x y hx hy ↦ degreeTiltRemainder_norm_le q hb x y hx hy) he
    (by dsimp only [b]; apply Eq.le; ring)
  refine ⟨θ, ?_, hθ.trans hb₁, hθ⟩
  rw [degreeTilt_eq]
  apply sub_eq_zero.mp
  calc
    _ = r + A *ᵥ θ + degreeTiltRemainder q θ := by dsimp only [r, A]; abel
    _ = 0 := hroot

end BoundedEdgeRegularSubgraphs
