module

public import BoundedEdgeRegularSubgraphs.FourierModes
public import BoundedEdgeRegularSubgraphs.ScalarAtoms
import BoundedEdgeRegularSubgraphs.BernoulliFourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# Scalar modulus bounds in the additive circle
-/

@[expose] public section

namespace BoundedEdgeRegularSubgraphs

/-- The Bernoulli Fourier factor as a function of a phase modulo (2π). -/
noncomputable def phaseBernoulliFactor (q : ℝ) (s : PhaseCircle) : ℂ :=
  1 - (q : ℂ) + (q : ℂ) * fourier 1 s

private theorem exists_representative_abs_eq (t : PhaseCircle) :
    ∃ x : ℝ, (x : PhaseCircle) = t ∧ |x| = ‖t‖ := by
  obtain ⟨x⟩ := t
  let j : ℤ := round ((2 * Real.pi)⁻¹ * x)
  refine ⟨x - (j : ℝ) * (2 * Real.pi), ?_, ?_⟩
  · change ((x - (j : ℝ) * (2 * Real.pi) : ℝ) : PhaseCircle) = (x : PhaseCircle)
    rw [AddCircle.coe_sub, ← zsmul_eq_mul, AddCircle.coe_zsmul, AddCircle.coe_period,
      smul_zero, sub_zero]
  · change |x - (j : ℝ) * (2 * Real.pi)| = ‖(x : PhaseCircle)‖
    rw [AddCircle.norm_eq]

theorem phase_norm_le_pi (t : PhaseCircle) : ‖t‖ ≤ Real.pi := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have h := AddCircle.norm_le_half_period (2 * Real.pi) (x := t) hπ.ne'
  rw [abs_of_nonneg hπ.le] at h
  linarith

private theorem sin_sq_half_abs (x : ℝ) :
    Real.sin (x / 2) ^ 2 = Real.sin (|x| / 2) ^ 2 := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, neg_div, Real.sin_neg, neg_sq]

/-- The exact scalar modulus formula with the torus distance to zero. -/
theorem phaseBernoulliFactor_norm_sq (q : ℝ) (t : PhaseCircle) :
    ‖phaseBernoulliFactor q t‖ ^ 2 = 1 - 4 * q * (1 - q) * Real.sin (‖t‖ / 2) ^ 2 := by
  obtain ⟨x, hx, hn⟩ := exists_representative_abs_eq t
  have he : phaseBernoulliFactor q (x : PhaseCircle) = bernoulliFourierFactor q x := by
    rw [phaseBernoulliFactor, fourier_one_coe, bernoulliFourierFactor]
  rw [← hn, ← hx, he, bernoulliFourierFactor_norm_sq, sin_sq_half_abs]

/-- The exponential upper bound on one factor, written on the torus. -/
theorem phaseBernoulliFactor_norm_le_exp (q : ℝ) (t : PhaseCircle) :
    ‖phaseBernoulliFactor q t‖ ≤ Real.exp (-2 * q * (1 - q) * Real.sin (‖t‖ / 2) ^ 2) := by
  obtain ⟨x, hx, hn⟩ := exists_representative_abs_eq t
  have he : phaseBernoulliFactor q (x : PhaseCircle) = bernoulliFourierFactor q x := by
    rw [phaseBernoulliFactor, fourier_one_coe, bernoulliFourierFactor]
  rw [← hn, ← hx, he, ← sin_sq_half_abs]
  exact bernoulliFourierFactor_norm_le q x

private theorem phase_norm_sub_pi (t : PhaseCircle) :
    ‖t - (Real.pi : PhaseCircle)‖ = Real.pi - ‖t‖ := by
  obtain ⟨x, hx, hn⟩ := exists_representative_abs_eq t
  have hxπ : |x| ≤ Real.pi := hn.trans_le (phase_norm_le_pi t)
  have hπ : 0 < Real.pi := Real.pi_pos
  have hper : 0 < 2 * Real.pi := by positivity
  have hnorm (y : ℝ) (hy : |y| ≤ Real.pi) : ‖(y : PhaseCircle)‖ = |y| := by
    apply (AddCircle.norm_coe_eq_abs_iff _ hper.ne').mpr
    rwa [abs_of_nonneg hper.le, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [← hn, ← hx, ← AddCircle.coe_sub]
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h] at hxπ ⊢
    have hle : x - Real.pi ≤ 0 := by linarith
    rw [hnorm (x - Real.pi) (by rw [abs_of_nonpos hle]; linarith), abs_of_nonpos hle]
    ring
  · rw [abs_of_nonpos h] at hxπ ⊢
    have he : ((x - Real.pi : ℝ) : PhaseCircle) = ((x + Real.pi : ℝ) : PhaseCircle) := by
      rw [show x + Real.pi = (x - Real.pi) + 2 * Real.pi by ring, AddCircle.coe_add,
        AddCircle.coe_period, add_zero]
    have hge : 0 ≤ x + Real.pi := by linarith
    rw [he, hnorm (x + Real.pi) (by rw [abs_of_nonneg hge]; linarith), abs_of_nonneg hge]
    ring

/-- Every replacement phase at distance at least `r` from the antipode has
a Bernoulli modulus at least `r / π`. -/
theorem phaseBernoulliFactor_norm_ge_antipode (q : ℝ) (t : PhaseCircle) :
    ‖t - (Real.pi : PhaseCircle)‖ / Real.pi ≤ ‖phaseBernoulliFactor q t‖ := by
  rw [phase_norm_sub_pi]
  have ht : ‖t‖ / 2 ≤ Real.pi / 2 := by linarith [phase_norm_le_pi t]
  have hcos : 0 ≤ Real.cos (‖t‖ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [norm_nonneg t, Real.pi_pos], ht⟩
  have hs : Real.cos (‖t‖ / 2) ≤ ‖phaseBernoulliFactor q t‖ := by
    apply (sq_le_sq₀ hcos (norm_nonneg _)).mp
    rw [phaseBernoulliFactor_norm_sq]
    nlinarith only [Real.sin_sq_add_cos_sq (‖t‖ / 2),
      mul_nonneg (sq_nonneg (q - 1 / 2)) (sq_nonneg (Real.sin (‖t‖ / 2)))]
  refine le_trans ?_ hs
  have h := Real.mul_le_sin (x := (Real.pi - ‖t‖) / 2)
    (by linarith [phase_norm_le_pi t]) (by linarith [norm_nonneg t])
  rw [show (Real.pi - ‖t‖) / 2 = Real.pi / 2 - ‖t‖ / 2 by ring,
    Real.sin_pi_div_two_sub] at h
  convert h using 1
  ring

/-- Moving an edge phase from above `7η` to at most `4η` gains a uniform
factor bounded away from one. -/
theorem phaseBernoulliFactor_compare_replacement {η lower : ℝ}
    (hη : 0 < η) (hη' : 7 * η ≤ Real.pi) (hlower : 0 < lower) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (q : ℝ) (s t : PhaseCircle),
      lower ≤ q * (1 - q) → 7 * η ≤ ‖s‖ → ‖t‖ ≤ 4 * η →
        ‖phaseBernoulliFactor q s‖ ≤ Real.exp (-γ) * ‖phaseBernoulliFactor q t‖ := by
  let Δ := Real.sin (7 * η / 2) ^ 2 - Real.sin (4 * η / 2) ^ 2
  have hsin (x : ℝ) (h0 : 0 ≤ x) (hπ : x ≤ Real.pi / 2) : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have hmono {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ Real.pi / 2) (hxy : x ≤ y) :
      Real.sin x ^ 2 ≤ Real.sin y ^ 2 :=
    (sq_le_sq₀ (hsin x hx (hxy.trans hy)) (hsin y (hx.trans hxy) hy)).mpr
      (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hy hxy)
  have hΔ : 0 < Δ := by
    apply sub_pos.mpr
    have h₁ : 0 ≤ Real.sin (4 * η / 2) := hsin _ (by positivity) (by linarith)
    have h₂ : 0 ≤ Real.sin (7 * η / 2) := hsin _ (by positivity) (by linarith)
    apply (sq_lt_sq₀ h₁ h₂).mpr
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith) (by linarith)
  refine ⟨2 * lower * Δ, by positivity, ?_⟩
  intro q s t hw hs ht
  let L := ‖phaseBernoulliFactor q s‖
  let R := ‖phaseBernoulliFactor q t‖
  have hw₀ : 0 ≤ q * (1 - q) := hlower.le.trans hw
  have h_s := hmono (x := 7 * η / 2) (y := ‖s‖ / 2)
    (by positivity) (by linarith [phase_norm_le_pi s]) (by linarith)
  have h_t := hmono (x := ‖t‖ / 2) (y := 4 * η / 2)
    (by positivity) (by linarith) (by linarith)
  have hdiff : Δ ≤ Real.sin (‖s‖ / 2) ^ 2 - Real.sin (‖t‖ / 2) ^ 2 := by
    dsimp [Δ]
    linarith only [h_s, h_t]
  have hR : R ^ 2 ≤ 1 := by
    dsimp only [R]
    rw [phaseBernoulliFactor_norm_sq]
    nlinarith only [mul_nonneg hw₀ (sq_nonneg (Real.sin (‖t‖ / 2)))]
  have hsq : L ^ 2 ≤ (Real.exp (-(2 * lower * Δ)) * R) ^ 2 := by
    have hdiff' : 4 * lower * Δ ≤ 4 * (q * (1 - q)) *
        (Real.sin (‖s‖ / 2) ^ 2 - Real.sin (‖t‖ / 2) ^ 2) :=
      mul_le_mul (by linarith only [hw]) hdiff hΔ.le (mul_nonneg (by norm_num) hw₀)
    have hLR : L ^ 2 ≤ R ^ 2 - 4 * lower * Δ := by
      dsimp only [L, R]
      rw [phaseBernoulliFactor_norm_sq, phaseBernoulliFactor_norm_sq]
      nlinarith only [hdiff']
    calc
      _ ≤ R ^ 2 - 4 * lower * Δ := hLR
      _ ≤ (1 - 4 * lower * Δ) * R ^ 2 := by
        nlinarith only [mul_nonneg (show 0 ≤ 4 * lower * Δ by positivity) (sub_nonneg.mpr hR)]
      _ ≤ Real.exp (-(4 * lower * Δ)) * R ^ 2 :=
        mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg _) (sq_nonneg _)
      _ = _ := by
        rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
        congr 2
        ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))).mp hsq

end BoundedEdgeRegularSubgraphs
