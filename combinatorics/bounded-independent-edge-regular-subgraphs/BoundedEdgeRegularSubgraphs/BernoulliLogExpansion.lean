module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-!
# The Bernoulli log expansion through degree four
-/

@[expose] public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

private noncomputable def expRemainder₂ (z : ℂ) : ℂ := 1 / 2 + z / 6 + z ^ 2 / 24

private noncomputable def expPolynomial (z : ℂ) : ℂ := z + z ^ 2 * expRemainder₂ z

/-- The degree-four cumulant polynomial of a Bernoulli variable. -/
noncomputable def bernoulliCumulantPolynomial (q z : ℂ) : ℂ :=
  q * z + q * (1 - q) * z ^ 2 / 2 +
    q * (1 - q) * (1 - 2 * q) * z ^ 3 / 6 +
    q * (1 - q) * (1 - 6 * q * (1 - q)) * z ^ 4 / 24

private noncomputable def logExpPolynomialTail (q z : ℂ) : ℂ :=
  let R := expRemainder₂ z
  let D := 1 / 6 + z / 24
  (-(q ^ 2 / 2) * (2 / 24 + D * (R + 1 / 2))) +
    (q ^ 3 / 3) * (3 * D + 3 * R ^ 2 + z * R ^ 3) -
    (q ^ 4 / 4) * (4 * R + 6 * z * R ^ 2 + 4 * z ^ 2 * R ^ 3 + z ^ 3 * R ^ 4)

private theorem logTaylor_expPolynomial (q z : ℂ) :
    Complex.logTaylor 5 (q * expPolynomial z) =
      bernoulliCumulantPolynomial q z + z ^ 5 * logExpPolynomialTail q z := by
  simp only [Complex.logTaylor, Finset.sum_range_succ]
  norm_num [expPolynomial, expRemainder₂, bernoulliCumulantPolynomial, logExpPolynomialTail]
  ring

private theorem norm_expRemainder₂_le_one (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖expRemainder₂ z‖ ≤ 1 := by
  have hsq : ‖z‖ ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ (norm_nonneg _) hz 2
  unfold expRemainder₂
  have h₁ := norm_add_le ((1 / 2 : ℂ) + z / 6) (z ^ 2 / 24)
  have h₂ := norm_add_le (1 / 2 : ℂ) (z / 6)
  simp only [norm_div, norm_pow, norm_one, Complex.norm_ofNat] at h₁ h₂
  linarith only [h₁, h₂, hsq, hz]

private theorem norm_expPolynomial_le (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖expPolynomial z‖ ≤ 2 * ‖z‖ := by
  unfold expPolynomial
  calc
    _ ≤ ‖z‖ + ‖z‖ ^ 2 * ‖expRemainder₂ z‖ := by
      have h := norm_add_le z (z ^ 2 * expRemainder₂ z)
      rw [Complex.norm_mul, Complex.norm_pow] at h
      exact h
    _ ≤ _ := by
      have h₁ := mul_le_of_le_one_right (sq_nonneg ‖z‖) (norm_expRemainder₂_le_one z hz)
      have h₂ := mul_le_mul_of_nonneg_left hz (norm_nonneg z)
      nlinarith only [h₁, h₂]

private theorem norm_pow_sub_pow_le_of_unit {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (m : ℕ) :
    ‖a ^ m - b ^ m‖ ≤ (m : ℝ) * ‖a - b‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ, show a ^ m * a - b ^ m * b =
      (a ^ m - b ^ m) * a + b ^ m * (a - b) by ring]
    calc
      _ ≤ ‖a ^ m - b ^ m‖ * ‖a‖ + ‖b‖ ^ m * ‖a - b‖ := by
        simpa only [norm_mul, norm_pow] using
          norm_add_le ((a ^ m - b ^ m) * a) (b ^ m * (a - b))
      _ ≤ ‖a ^ m - b ^ m‖ + ‖a - b‖ := by
        apply add_le_add (mul_le_of_le_one_right (norm_nonneg _) ha)
        apply mul_le_of_le_one_left (norm_nonneg _)
        simpa using pow_le_pow_left₀ (norm_nonneg _) hb m
      _ ≤ _ := by
        rw [Nat.cast_succ, add_mul, one_mul]
        exact add_le_add ih le_rfl

private theorem logTaylor_five_lipschitz {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖Complex.logTaylor 5 a - Complex.logTaylor 5 b‖ ≤ 5 * ‖a - b‖ := by
  unfold Complex.logTaylor
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _ ∈ Finset.range 5, ‖a - b‖ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j = 0
      · subst j; simp
      rw [← sub_div, ← mul_sub, norm_div, norm_mul, norm_pow, norm_neg, norm_one,
        one_pow, one_mul, Complex.norm_natCast]
      apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hj))).mpr
      rw [mul_comm ‖a - b‖]
      exact norm_pow_sub_pow_le_of_unit ha hb j
    _ = _ := by simp

private theorem norm_exp_sub_polynomial (z : ℂ) :
    ‖Complex.exp z - 1 - expPolynomial z‖ ≤ ‖z‖ ^ 5 * Real.exp ‖z‖ := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp z 5
  have he : (∑ j ∈ Finset.range 5, z ^ j / (j.factorial : ℂ)) = 1 + expPolynomial z := by
    simp only [Finset.sum_range_succ]
    norm_num [expPolynomial, expRemainder₂, Nat.factorial]
    ring
  rwa [he, ← sub_sub] at h

private theorem logExpPolynomialTail_uniform :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (q : ℝ) (z : ℂ), q ∈ Set.Icc (0 : ℝ) 1 → ‖z‖ ≤ 1 →
      ‖logExpPolynomialTail q z‖ ≤ M := by
  let K := Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : ℂ) 1
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  let F (p : ℝ × ℂ) := logExpPolynomialTail p.1 p.2
  have hF : Continuous F := by dsimp [F, logExpPolynomialTail, expRemainder₂]; fun_prop
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max 0 M, le_max_left _ _, ?_⟩
  intro q z hq hz
  exact (hM (q, z) ⟨hq, by simpa [Metric.mem_closedBall, dist_eq_norm] using hz⟩).trans
    (le_max_right _ _)

/-- The uniform scalar fourth-order expansion, with a fifth-order norm remainder.
For Fourier phases the argument is imaginary and the linear term is removed by centring. -/
theorem bernoulli_log_expansion :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℝ) (z : ℂ), q ∈ Set.Icc (0 : ℝ) 1 → ‖z‖ ≤ 1 / 4 →
      ‖Complex.log (1 - (q : ℂ) + (q : ℂ) * Complex.exp z) -
        bernoulliCumulantPolynomial q z‖ ≤ C * ‖z‖ ^ 5 := by
  obtain ⟨M, hM₀, hM⟩ := logExpPolynomialTail_uniform
  refine ⟨64 + 5 * Real.exp 1 + M, by positivity, ?_⟩
  intro q z hq hz
  have hz₁ : ‖z‖ ≤ 1 := hz.trans (by norm_num)
  let u : ℂ := (q : ℂ) * (Complex.exp z - 1)
  let v : ℂ := (q : ℂ) * expPolynomial z
  have hqnorm : ‖(q : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hq.1]
    exact hq.2
  have hu : ‖u‖ ≤ 2 * ‖z‖ := by
    dsimp only [u]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hqnorm).trans (Complex.norm_exp_sub_one_le hz₁)
  have hv : ‖v‖ ≤ 2 * ‖z‖ := by
    dsimp only [v]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hqnorm).trans (norm_expPolynomial_le z hz₁)
  have hu₂ : ‖u‖ ≤ 1 / 2 := by linarith only [hu, hz]
  have hv₁ : ‖v‖ ≤ 1 := by linarith only [hv, hz]
  have huv : ‖u - v‖ ≤ ‖z‖ ^ 5 * Real.exp 1 := by
    dsimp only [u, v]
    rw [← mul_sub, norm_mul]
    calc
      _ ≤ _ := mul_le_of_le_one_left (norm_nonneg _) hqnorm
      _ ≤ _ := norm_exp_sub_polynomial z
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hz₁) (by positivity)
  have hlog : ‖Complex.log (1 + u) - Complex.logTaylor 5 u‖ ≤ 64 * ‖z‖ ^ 5 := by
    have h := Complex.norm_log_sub_logTaylor_le 4 (z := u) (hu₂.trans_lt (by norm_num))
    norm_num at h
    have hpos : 0 < 1 - ‖u‖ := by linarith
    have hi : (1 - ‖u‖)⁻¹ ≤ 2 := by
      apply (inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 2)).mpr
      norm_num
      linarith only [hu₂]
    have hpow := pow_le_pow_left₀ (norm_nonneg u) hu 5
    calc
      _ ≤ ‖u‖ ^ 5 * (1 - ‖u‖)⁻¹ / 5 := h
      _ ≤ (2 * ‖z‖) ^ 5 * 2 / 5 :=
        div_le_div_of_nonneg_right
          (mul_le_mul hpow hi (inv_nonneg.mpr hpos.le) (by positivity)) (by norm_num)
      _ ≤ _ := by
        rw [mul_pow]
        nlinarith only [pow_nonneg (norm_nonneg z) 5]
  have hlip := (logTaylor_five_lipschitz (hu₂.trans (by norm_num)) hv₁).trans
    (mul_le_mul_of_nonneg_left huv (by norm_num : (0 : ℝ) ≤ 5))
  have htail : ‖Complex.logTaylor 5 v - bernoulliCumulantPolynomial q z‖ ≤ M * ‖z‖ ^ 5 := by
    dsimp only [v]
    rw [logTaylor_expPolynomial, add_sub_cancel_left, norm_mul, norm_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM q z hq hz₁) (by positivity)
  rw [show 1 - (q : ℂ) + (q : ℂ) * Complex.exp z = 1 + u by dsimp [u]; ring]
  rw [show Complex.log (1 + u) - bernoulliCumulantPolynomial q z =
    (Complex.log (1 + u) - Complex.logTaylor 5 u) +
      (Complex.logTaylor 5 u - Complex.logTaylor 5 v) +
      (Complex.logTaylor 5 v - bernoulliCumulantPolynomial q z) by ring]
  have h₁ := norm_add_le (Complex.log (1 + u) - Complex.logTaylor 5 u +
    (Complex.logTaylor 5 u - Complex.logTaylor 5 v))
    (Complex.logTaylor 5 v - bernoulliCumulantPolynomial q z)
  have h₂ := norm_add_le (Complex.log (1 + u) - Complex.logTaylor 5 u)
    (Complex.logTaylor 5 u - Complex.logTaylor 5 v)
  nlinarith only [h₁, h₂, hlog, hlip, htail]

end BoundedEdgeRegularSubgraphs
