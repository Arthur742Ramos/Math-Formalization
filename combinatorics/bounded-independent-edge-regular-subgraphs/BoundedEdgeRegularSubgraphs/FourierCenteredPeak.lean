module

public import BoundedEdgeRegularSubgraphs.FourierGaussianError
public import BoundedEdgeRegularSubgraphs.FourierUniformBoxCost
public import BoundedEdgeRegularSubgraphs.GaussianCubicUniform
public import BoundedEdgeRegularSubgraphs.GaussianQuarticUniform
import Mathlib.Tactic

/-!
# Uniform approximation of the centred Fourier peak
-/

public section

open Filter MeasureTheory Matrix Set
open scoped BigOperators MatrixOrder Topology

namespace BoundedEdgeRegularSubgraphs

theorem full_degreeCovariance_posDef_of_floor {n : ℕ} (hn : 3 ≤ n)
    (q : Edge (Fin n) → Icc (0 : ℝ) 1) {l : ℝ} (hl : 0 < l)
    (hq : ∀ e, l ≤ (q e : ℝ) * (1 - q e)) :
    let Q := degreeCovariance Finset.univ q
    Q.PosDef ∧ ∀ x : Fin n → ℝ, l * (n : ℝ) / 3 * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (Q *ᵥ x) := by
  let Q := degreeCovariance Finset.univ q
  have hnℝ : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hquad (x : Fin n → ℝ) : l * (n : ℝ) / 3 * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (Q *ᵥ x) := by
    have h := (degreeCovariance_univ_bounds q l hl.le hq x).1
    rw [Fintype.card_fin] at h
    rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
    refine le_trans ?_ h
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun i _ ↦ sq_nonneg (x i))
    nlinarith only [mul_nonneg hl.le (sub_nonneg.mpr hnℝ)]
  have hHerm : Q.IsHermitian := by
    ext i j
    simp only [Q, degreeCovariance, conjTranspose_apply, star_trivial]
    exact Finset.sum_congr rfl (fun e _ ↦ by ring)
  refine ⟨Matrix.PosDef.of_dotProduct_mulVec_pos hHerm ?_, hquad⟩
  intro x hx
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    contrapose! hx
    exact funext hx
  have hsum : 0 < ∑ j, x j ^ 2 := Finset.sum_pos' (fun _ _ ↦ sq_nonneg _)
    ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  have hpos : 0 < l * (n : ℝ) / 3 := by have := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) hnℝ; positivity
  rw [star_trivial]
  exact (mul_pos hpos hsum).trans_le (hquad x)

/-- The full-array Gaussian motions have uniformly bounded means and a
uniform approximation for the complex Fourier integral on the small box. -/
theorem eventually_centered_peak_sub_le_uniform {l : ℝ} (hl : 0 < l) :
    ∃ U M : ℝ, 0 < U ∧ 0 ≤ M ∧ ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      ∀ (q : Edge (Fin k) → Icc (0 : ℝ) 1) (d : Fin k → ℤ),
        (∀ e, l ≤ (q e : ℝ) * (1 - q e)) →
        (∀ i, (d i : ℝ) = degreeSum (fun e ↦ (q e : ℝ)) i) →
        let A : Finset (Edge (Fin k)) := Finset.univ
        let Ξ := phaseGaussianScale (degreeCovariance A q)
        let μ := phaseGaussianCubicSecondMoment A q
        let ν := phaseGaussianQuarticMean A q
        0 ≤ μ ∧ μ ≤ U ∧ |ν| ≤ M ∧
          ‖(∫ t in phaseBox (0 : PhaseCircle) (fourierBoxRadius k), degreeFourier A q d t ∂phaseLaw) -
            ((Ξ * Real.exp (-μ / 2 + ν) : ℝ) : ℂ)‖ ≤ ε * Ξ := by
  obtain ⟨U, V, hU, hV, hCubic⟩ := gaussianCubic_character_uniform hl
    (K := 1 / 24) (by norm_num)
  obtain ⟨M, hM, hQuartic⟩ := eventually_gaussian_quartic_box_weight_sub_le
    (a := 3 / l) (K := 1 / 96) (by positivity) (by norm_num)
  refine ⟨U, M, hU, hM, ?_⟩
  intro ε hε
  let z := min 1 (ε / (4 * (Real.exp M + 1)))
  have hz₀ : 0 < z := lt_min zero_lt_one (by positivity)
  have hz₁ : z ≤ 1 := min_le_left _ _
  have hzε : z ≤ ε / (4 * (Real.exp M + 1)) := min_le_right _ _
  have hs : Tendsto (fun k : ℕ ↦ V / Real.sqrt k) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := V)).mul (tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop :
        Tendsto (fun k : ℕ ↦ (k : ℝ)) atTop atTop)))
    simpa only [div_eq_mul_inv, Function.comp_apply, mul_zero] using h
  filter_upwards [hQuartic z hz₀, eventually_degreeFourierLocalError_le hz₀,
    hs.eventually_lt_const hz₀, eventually_ge_atTop (3 : ℕ)] with k h₄ hR hV' hk
  intro q d hq hd
  let A : Finset (Edge (Fin k)) := Finset.univ
  let Q := degreeCovariance A q
  let B := (CFC.sqrt Q)⁻¹
  let a (e : Edge (Fin k)) := degreeCubicCoefficient (q e)
  let b (e : Edge (Fin k)) := degreeQuarticCoefficient (q e)
  let r := fourierBoxRadius k
  let γ := standardGaussianProduct k
  let μ := phaseGaussianCubicSecondMoment A q
  let ν := phaseGaussianQuarticMean A q
  let Ξ := phaseGaussianScale Q
  obtain ⟨hQ, hQuad⟩ := full_degreeCovariance_posDef_of_floor hk q hl hq
  have hkl : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  obtain ⟨hB, hRows⟩ := gaussian_inverse_sqrt_bounds Q hQ (by positivity : 0 < l * (k : ℝ) / 3) hQuad
  have he : (l * (k : ℝ) / 3)⁻¹ = 3 / l / k := by field_simp [hl.ne', hkl.ne']
  simp only [he] at hB hRows
  obtain ⟨hν, h₄'⟩ := h₄ A b B (fun e _ ↦ abs_degreeQuarticCoefficient_le (q e)) hRows hB
  have h₃ : 0 ≤ μ ∧ μ ≤ U ∧
      ‖(∫ x, realCharacter 1 (phaseGaussianCubic A q x) ∂γ) - (Real.exp (-μ / 2) : ℂ)‖ ≤
        V / Real.sqrt k := by
    cases k with
    | zero => omega
    | succ n =>
      have hc := hCubic n hk q a hq (fun e ↦ abs_degreeCubicCoefficient_le (q e))
      have heval (x : Fin (n + 1) → ℝ) :
          MvPolynomial.eval x (gaussianCubicPolynomial A a (fun e ↦ B *ᵥ realIncidence e)) =
            phaseGaussianCubic A q x := by
        rw [eval_gaussianCubicPolynomial]
        change _ = ∑ e ∈ A, a e * ((B *ᵥ x) e.val.1 + (B *ᵥ x) e.val.2) ^ 3
        exact Finset.sum_congr rfl (fun e _ ↦ by rw [dotProduct_gaussian_whitened_edge Q])
      let G := gaussianCubicPolynomial A a (fun e ↦ B *ᵥ realIncidence e)
      let v := ∫ x, MvPolynomial.eval x G ^ 2 ∂γ
      change 0 ≤ v ∧ v ≤ U ∧
        ‖(∫ x, realCharacter 1 (MvPolynomial.eval x G) ∂γ) - (Real.exp (-v / 2) : ℂ)‖ ≤
          V / Real.sqrt (n + 1 : ℕ) at hc
      dsimp only [v, G] at hc
      simp_rw [heval] at hc
      exact hc
  have h := norm_centered_peak_sub_le q d hd hQ hR.1 hR.2.1 hz₀.le hz₁
    (hR.2.2 A q) hν h₄' (h₃.2.2.trans hV'.le)
  refine ⟨h₃.1, h₃.2.1, hν, h.trans ?_⟩
  have hΞ : 0 ≤ Ξ := by dsimp only [Ξ]; rw [phaseGaussianScale_eq Q hQ]; positivity
  change Ξ * _ ≤ ε * Ξ
  rw [mul_comm ε Ξ]
  apply mul_le_mul_of_nonneg_left _ hΞ
  have h₁ := mul_le_mul_of_nonneg_left hz₁ (show (0 : ℝ) ≤ 2 * z by positivity)
  have h₂ := (le_div_iff₀ (show 0 < 4 * (Real.exp M + 1) by positivity)).mp hzε
  nlinarith only [h₁, h₂, mul_nonneg hz₀.le (Real.exp_nonneg M)]

end BoundedEdgeRegularSubgraphs
