module

public import BoundedEdgeRegularSubgraphs.CentringTilt
import BoundedEdgeRegularSubgraphs.MeanDrift
import BoundedEdgeRegularSubgraphs.RegularAtomUpper
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# The Euclidean bound on a centring tilt
-/

public section

open scoped BigOperators Matrix

namespace BoundedEdgeRegularSubgraphs

private theorem tilt_change_mul_ge (q : Set.Icc (0 : ℝ) 1) {s l : ℝ} (hs : |s| ≤ 2)
    (hl : ∀ u : ℝ, |u| ≤ 2 → l ≤ (tiltProb q u : ℝ) * (1 - (tiltProb q u : ℝ))) :
    l * s ^ 2 ≤ ((tiltProb q s : ℝ) - q) * s := by
  let I := Set.Icc (-2 : ℝ) 2
  let f (x : ℝ) := (tiltProb q x : ℝ) - l * x
  let g (x : ℝ) := (tiltProb q x : ℝ) * (1 - (tiltProb q x : ℝ)) - l
  have fd (x : ℝ) : HasDerivAt f (g x) x := by
    change HasDerivAt ((fun y ↦ (tiltProb q y : ℝ)) - fun y ↦ l * y) (g x) x
    exact (hasDerivAt_tiltProb q x).sub
      (by simpa only [mul_one, id_eq] using (hasDerivAt_id x).const_mul l)
  have hmono : MonotoneOn f I :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun x _ ↦ (fd x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (fd x).hasDerivWithinAt)
      (fun x hx ↦ by
        have hx' : x ∈ I := interior_subset hx
        exact sub_nonneg.mpr (hl x (abs_le.mpr hx')))
  have hs' : s ∈ I := abs_le.mp hs
  have hz : (0 : ℝ) ∈ I := by norm_num [I]
  have hzero : f 0 = (q : ℝ) := by simp [f]
  rcases le_total 0 s with hn | hn
  · have h := hmono hz hs' hn
    change f 0 ≤ (tiltProb q s : ℝ) - l * s at h
    rw [hzero] at h
    nlinarith only [mul_le_mul_of_nonneg_right h hn]
  · have h := hmono hs' hz hn
    change (tiltProb q s : ℝ) - l * s ≤ f 0 at h
    rw [hzero] at h
    nlinarith only [mul_le_mul_of_nonpos_right h hn]

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- A positive variance bound on the tilt cube gives the squared Euclidean
norm estimate for the potentials in Lemma 2.1. -/
theorem vertexTilt_squared_norm_le (q : Edge α → Set.Icc (0 : ℝ) 1)
    (θ : α → ℝ) (hθ : ‖θ‖ ≤ 1) (hn : 3 ≤ Fintype.card α) {l : ℝ} (hl : 0 < l)
    (hv : ∀ (e : Edge α) (s : ℝ), |s| ≤ 2 →
      l ≤ (tiltProb (q e) s : ℝ) * (1 - (tiltProb (q e) s : ℝ))) :
    (∑ i, θ i ^ 2) ≤
      (∑ i, (degreeSum (fun e ↦ (vertexTilt q θ e : ℝ)) i -
        degreeSum (fun e ↦ (q e : ℝ)) i) ^ 2) / (l * ((Fintype.card α : ℝ) - 2)) ^ 2 := by
  set v : α → ℝ := fun i ↦ degreeSum (fun e ↦ (vertexTilt q θ e : ℝ)) i -
    degreeSum (fun e ↦ (q e : ℝ)) i
  let w (e : Edge α) := (vertexTilt q θ e : ℝ) - (q e : ℝ)
  let S := ∑ i, θ i ^ 2
  let T := ∑ i, v i ^ 2
  let a := l * ((Fintype.card α : ℝ) - 2)
  have hN : (3 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  have ha : 0 < a := mul_pos hl (by linarith)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hv' (i : α) : v i = degreeSum w i := by
    simp only [v, degreeSum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    unfold w
    split_ifs <;> simp
  have hs (e : Edge α) : |θ e.val.1 + θ e.val.2| ≤ 2 := by
    have h (i : α) : |θ i| ≤ 1 := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm _ _).trans hθ
    exact (abs_add_le _ _).trans (by linarith only [h e.val.1, h e.val.2])
  have hsum : l * (∑ e : Edge α, (θ e.val.1 + θ e.val.2) ^ 2) ≤ ∑ i, θ i * v i := by
    simp_rw [hv']
    rw [weighted_degree_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    rw [mul_comm (θ e.val.1 + θ e.val.2)]
    exact tilt_change_mul_ge (q e) (hs e) (hv e)
  have hlo : a * S ≤ ∑ i, θ i * v i := by
    rw [sum_edge_squares, mul_add, ← mul_assoc] at hsum
    exact (le_add_of_nonneg_right (mul_nonneg hl.le (sq_nonneg _))).trans hsum
  change S ≤ T / a ^ 2
  rcases hS.eq_or_lt with hS' | hS'
  · rw [← hS']
    exact div_nonneg hT (sq_nonneg _)
  have hdot : 0 ≤ ∑ i, θ i * v i := (mul_nonneg ha.le hS).trans hlo
  have hsq := (sq_le_sq₀ (mul_nonneg ha.le hS) hdot).mpr hlo
  have hcs : (∑ i, θ i * v i) ^ 2 ≤ S * T := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ θ v
  have hmul : (S * a ^ 2) * S ≤ T * S := by nlinarith only [hsq.trans hcs]
  exact (le_div_iff₀ (sq_pos_of_pos ha)).mpr (le_of_mul_le_mul_right hmul hS')

/-- The centring tilt stays uniformly inside the probability interval and
has both norm estimates from Lemma 2.1. -/
theorem exists_centered_vertexTilt_quantitative (ξ : ℝ) (hξ : 0 < ξ) (hξ' : ξ < 1 / 2) :
    ∃ δ ε C : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ 0 < ε ∧ 0 < C ∧
      ∀ {α : Type*} [Fintype α] [LinearOrder α], 3 ≤ Fintype.card α →
      ∀ (q : Edge α → Set.Icc (0 : ℝ) 1) (d : α → ℝ),
      (∀ e, ξ ≤ (q e : ℝ) ∧ (q e : ℝ) ≤ 1 - ξ) →
      ‖degreeSum (fun e ↦ (q e : ℝ)) - d‖ ≤ ε * Fintype.card α →
      ∃ θ : α → ℝ, degreeSum (fun e ↦ (vertexTilt q θ e : ℝ)) = d ∧
        (∀ e, δ ≤ (vertexTilt q θ e : ℝ) ∧ (vertexTilt q θ e : ℝ) ≤ 1 - δ) ∧
        ‖θ‖ ≤ C * ‖degreeSum (fun e ↦ (q e : ℝ)) - d‖ / Fintype.card α ∧
        (∑ i, θ i ^ 2) ≤ (C / (Fintype.card α : ℝ)) ^ 2 *
          ∑ i, (degreeSum (fun e ↦ (q e : ℝ)) i - d i) ^ 2 := by
  obtain ⟨δ, hδ, hδ', hfloor⟩ := exists_uniform_tilt_floor ξ hξ hξ'
  obtain ⟨ε, C₀, hε, hC₀, hcenter⟩ := exists_centered_vertexTilt ξ hξ hξ'
  let l := δ * (1 - δ)
  have hl : 0 < l := mul_pos hδ (by linarith)
  let C := max C₀ (3 / l)
  have hC : 0 < C := hC₀.trans_le (le_max_left _ _)
  refine ⟨δ, ε, C, hδ, hδ', hε, hC, ?_⟩
  intro β _ _ hn q d hq hd
  obtain ⟨θ, hdθ, hθ, hmax⟩ := hcenter hn q d hq hd
  let k : ℝ := Fintype.card β
  have hk : (3 : ℝ) ≤ k := by dsimp only [k]; exact_mod_cast hn
  have hk₀ : 0 < k := by linarith
  have hvar (e : Edge β) (s : ℝ) (hs : |s| ≤ 2) :
      l ≤ (tiltProb (q e) s : ℝ) * (1 - (tiltProb (q e) s : ℝ)) := by
    obtain ⟨h₁, h₂⟩ := hfloor (q e) s (hq e).1 (hq e).2 (hs.trans (by norm_num))
    dsimp only [l]
    nlinarith only [mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr h₂)]
  refine ⟨θ, hdθ, ?_, ?_, ?_⟩
  · intro e
    have h (i : β) : |θ i| ≤ 1 := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm _ _).trans hθ
    have hs : |θ e.val.1 + θ e.val.2| ≤ 20 :=
      (abs_add_le _ _).trans (by linarith only [h e.val.1, h e.val.2])
    exact hfloor (q e) _ (hq e).1 (hq e).2 hs
  · exact hmax.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) hk₀.le)
  · have hnorm := vertexTilt_squared_norm_le q θ hθ hn hl hvar
    rw [hdθ] at hnorm
    have hden : 0 < l * (k - 2) := mul_pos hl (by linarith)
    have hconst : 1 / (l * (k - 2)) ≤ C / k := by
      apply (div_le_div_iff₀ hden hk₀).mpr
      calc
        _ ≤ 3 * (k - 2) := by linarith only [hk]
        _ = (3 / l) * (l * (k - 2)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hden.le
    have hconst' := (sq_le_sq₀ (div_nonneg (by norm_num) hden.le) (div_nonneg hC.le hk₀.le)).mpr hconst
    let R : ℝ := ∑ i, (degreeSum (fun e ↦ (q e : ℝ)) i - d i) ^ 2
    have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
    have he : (∑ i, (d i - degreeSum (fun e ↦ (q e : ℝ)) i) ^ 2) = R := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he] at hnorm
    refine hnorm.trans ?_
    calc
      R / (l * (k - 2)) ^ 2 = (1 / (l * (k - 2))) ^ 2 * R := by
        rw [div_pow, one_pow, one_div, inv_mul_eq_div]
      _ ≤ _ := mul_le_mul_of_nonneg_right hconst' hR


end BoundedEdgeRegularSubgraphs
