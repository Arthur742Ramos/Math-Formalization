module

public import BoundedEdgeRegularSubgraphs.CenteredDegreeAtom
public import BoundedEdgeRegularSubgraphs.TiltQuantitative
import Mathlib.Tactic

/-!
# Lemma 2.1: centring and the tilted-atom lower bound
-/

public section

open Filter MeasureTheory Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- Uniform centring, likelihood cost and the degree-atom lower bound
for an integer target with even coordinate sum. -/
theorem eventually_vertexTilt_and_degreeAtom_lower {ξ : ℝ} (hξ : 0 < ξ) (hξ' : ξ < 1 / 2) :
    ∃ δ ε C : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ 0 < ε ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ (q : Edge (Fin k) → Icc (0 : ℝ) 1) (d : Fin k → ℤ),
        (∀ e, ξ ≤ (q e : ℝ) ∧ (q e : ℝ) ≤ 1 - ξ) → Even (∑ i, d i) →
        let r := degreeSum (fun e ↦ (q e : ℝ)) - fun i ↦ (d i : ℝ)
        ‖r‖ ≤ ε * k →
        ∃ θ : Fin k → ℝ,
          degreeSum (fun e ↦ (vertexTilt q θ e : ℝ)) = (fun i ↦ (d i : ℝ)) ∧
          (∀ e, δ ≤ (vertexTilt q θ e : ℝ) ∧ (vertexTilt q θ e : ℝ) ≤ 1 - δ) ∧
          ‖θ‖ ≤ C * ‖r‖ / k ∧
          (∑ i, θ i ^ 2) ≤ (C / (k : ℝ)) ^ 2 * ∑ i, r i ^ 2 ∧
          let K := (∑ i, θ i * (d i : ℝ)) - logPartition q θ
          0 ≤ K ∧ K ≤ C * (∑ i, r i ^ 2) / k ∧
          (graphLaw (vertexTilt q θ)).real (degreeAtom Finset.univ d) =
            Real.exp K * (graphLaw q).real (degreeAtom Finset.univ d) ∧
          Real.exp (-(k : ℝ) / 2 * Real.log k - C * k - C * (∑ i, r i ^ 2) / k) ≤
            (graphLaw q).real (degreeAtom Finset.univ d) := by
  obtain ⟨δ, ε, C₀, hδ, hδ', hε, hC₀, hTilt⟩ := exists_centered_vertexTilt_quantitative ξ hξ hξ'
  let l := δ * (1 - δ)
  have hl : 0 < l := mul_pos hδ (by linarith)
  obtain ⟨c, C₁, _, hC₁, hAtom⟩ := centered_degreeAtom_uniform_asymptotic_of_variance_floor hl
  let C := max C₀ (max C₁ (C₀ ^ 2 / 4))
  have hC : 0 < C := hC₀.trans_le (le_max_left _ _)
  have hC₁' : C₁ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC₀' : C₀ ≤ C := le_max_left _ _
  have hC₂' : C₀ ^ 2 / 4 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨δ, ε, C, hδ, hδ', hε, hC, ?_⟩
  filter_upwards [hAtom 1 zero_lt_one, eventually_ge_atTop (3 : ℕ)] with k hAtom' hk
  intro q d hq hEven r hr
  have hk₀ : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  obtain ⟨θ, hd, hδq, hθ, hθ₂⟩ := hTilt (α := Fin k)
    (by simpa only [Fintype.card_fin] using hk) q (fun i ↦ (d i : ℝ)) hq
    (by simpa only [Fintype.card_fin] using hr)
  simp only [Fintype.card_fin] at hθ hθ₂
  have hθ₂' : (∑ i, θ i ^ 2) ≤ (C₀ / (k : ℝ)) ^ 2 * ∑ i, r i ^ 2 := hθ₂
  let R := ∑ i, r i ^ 2
  have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ ↦ sq_nonneg (r i))
  refine ⟨θ, hd, hδq, hθ.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC₀' (norm_nonneg _)) hk₀.le), ?_, ?_⟩
  · exact hθ₂'.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀
      (div_nonneg hC₀.le hk₀.le) (div_le_div_of_nonneg_right hC₀' hk₀.le) 2) hR)
  let K := (∑ i, θ i * (d i : ℝ)) - logPartition q θ
  have hh := centered_vertexTilt_logLikelihood_bounds q θ (fun i ↦ (d i : ℝ)) hd
  have hK₀ : 0 ≤ K := hh.1
  have hscale : ((k : ℝ) - 1) / 4 * (∑ i, θ i ^ 2) ≤ C * R / k := by
    have hs : 0 ≤ ((k : ℝ) - 1) / 4 := by positivity
    calc
      _ ≤ (((k : ℝ) - 1) / 4) * ((C₀ / (k : ℝ)) ^ 2 * R) :=
        mul_le_mul_of_nonneg_left hθ₂' hs
      _ ≤ ((k : ℝ) / 4) * ((C₀ / (k : ℝ)) ^ 2 * R) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
      _ = (C₀ ^ 2 / 4) * R / k := by field_simp [hk₀.ne']
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC₂' hR) hk₀.le
  have hK : K ≤ C * R / k := by
    exact (by simpa only [Fintype.card_fin] using hh.2 : K ≤ _).trans hscale
  have hlaw : (graphLaw (vertexTilt q θ)).real (degreeAtom Finset.univ d) =
      Real.exp K * (graphLaw q).real (degreeAtom Finset.univ d) :=
    real_graphLaw_vertexTilt_degreeAtom q θ d
  refine ⟨hK₀, hK, hlaw, ?_⟩
  have hVar (e : Edge (Fin k)) : l ≤ (vertexTilt q θ e : ℝ) * (1 - vertexTilt q θ e) := by
    dsimp only [l]
    nlinarith only [mul_nonneg (sub_nonneg.mpr (hδq e).1) (sub_nonneg.mpr (hδq e).2)]
  have hP := (hAtom' (vertexTilt q θ) d hVar (congrFun hd.symm) hEven).2.2
  have h₀ : Real.exp (-(k : ℝ) / 2 * Real.log k - C₁ * k - K) ≤
      (graphLaw q).real (degreeAtom Finset.univ d) := by
    have h := mul_le_mul_of_nonneg_left hP (Real.exp_nonneg (-K))
    have hcancel : Real.exp (-K) * Real.exp K = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [hlaw, ← mul_assoc, hcancel, one_mul, ← Real.exp_add] at h
    refine le_trans (le_of_eq (congrArg Real.exp ?_)) h
    ring
  refine (Real.exp_le_exp.mpr ?_).trans h₀
  change -(k : ℝ) / 2 * Real.log k - C * k - C * R / k ≤ _
  linarith only [hK, mul_le_mul_of_nonneg_right hC₁' hk₀.le]

end BoundedEdgeRegularSubgraphs
