module

public import BoundedEdgeRegularSubgraphs.FourierGaussianError
public import BoundedEdgeRegularSubgraphs.FourierUniformBoxCost
public import BoundedEdgeRegularSubgraphs.GaussianCubicUniform
public import BoundedEdgeRegularSubgraphs.GaussianQuarticUniform
public import BoundedEdgeRegularSubgraphs.OverlapInverse
import Mathlib.Tactic

/-!
# The centred complex peak with available edges

The real-coordinate integrand centres each available Bernoulli variable.
It therefore also represents a mean degree vector with nonintegral entries.
-/

@[expose] public section

open Filter MeasureTheory Matrix Set
open scoped BigOperators MatrixOrder Topology

namespace BoundedEdgeRegularSubgraphs

/-- Centred characteristic integrand on real coordinates. -/
noncomputable def centeredDegreeFourierReal {n : ℕ}
    (A : Finset (Edge (Fin n))) (q : Edge (Fin n) → Icc (0 : ℝ) 1)
    (t : Fin n → ℝ) : ℂ :=
  ∏ e ∈ A, let z := ((t e.val.1 + t e.val.2 : ℝ) : ℂ) * Complex.I
    let p := ((q e : ℝ) : ℂ)
    Complex.exp (-(p * z)) * (1 - p + p * Complex.exp z)

/-- Factoring out the mean-degree phase gives the integrand in Appendix A. -/
theorem centeredDegreeFourierReal_eq_mean_phase {n : ℕ}
    (A : Finset (Edge (Fin n))) (q : Edge (Fin n) → Icc (0 : ℝ) 1)
    (t : Fin n → ℝ) :
    let z (e : Edge (Fin n)) := ((t e.val.1 + t e.val.2 : ℝ) : ℂ) * Complex.I
    centeredDegreeFourierReal A q t =
      Complex.exp (-(∑ e ∈ A, ((q e : ℝ) : ℂ) * z e)) *
        ∏ e ∈ A, (1 - ((q e : ℝ) : ℂ) + ((q e : ℝ) : ℂ) * Complex.exp (z e)) := by
  intro z
  unfold centeredDegreeFourierReal
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, Finset.sum_neg_distrib]

/-- The Lebesgue integral on the small real box with the Haar normalization. -/
noncomputable def centeredRealPeak {n : ℕ}
    (A : Finset (Edge (Fin n))) (q : Edge (Fin n) → Icc (0 : ℝ) 1) (r : ℝ) : ℂ :=
  (((2 * Real.pi) ^ n : ℝ) : ℂ)⁻¹ *
    ∫ t in realPhaseBox (α := Fin n) r, centeredDegreeFourierReal A q t

private theorem centeredDegreeFourierReal_expansion {n : ℕ}
    (A : Finset (Edge (Fin n))) (q : Edge (Fin n) → Icc (0 : ℝ) 1)
    (t : Fin n → ℝ) (ht : ∀ e ∈ A, |t e.val.1 + t e.val.2| ≤ 1 / 4) :
    let Q := degreeCovariance A q
    let f := edgeCubic A (fun e ↦ degreeCubicCoefficient (q e)) t
    let h := edgeQuartic A (fun e ↦ degreeQuarticCoefficient (q e)) t
    centeredDegreeFourierReal A q t =
      Real.exp (-(t ⬝ᵥ (Q *ᵥ t)) / 2) •
        (realCharacter 1 f * (Real.exp h : ℂ) * Complex.exp (degreeFourierLocalError A q t)) := by
  let s (e : Edge (Fin n)) := t e.val.1 + t e.val.2
  let w (e : Edge (Fin n)) := (q e : ℝ) * (1 - q e)
  let z (e : Edge (Fin n)) := (s e : ℂ) * Complex.I
  let P (e : Edge (Fin n)) := bernoulliCumulantPolynomial (q e : ℝ) (z e)
  let L (e : Edge (Fin n)) :=
    Complex.log (1 - ((q e : ℝ) : ℂ) + ((q e : ℝ) : ℂ) * Complex.exp (z e))
  let F := ∑ e ∈ A, degreeCubicCoefficient (q e) * s e ^ 3
  let H := ∑ e ∈ A, degreeQuarticCoefficient (q e) * s e ^ 4
  let Q := degreeCovariance A q
  let g := t ⬝ᵥ (Q *ᵥ t)
  let R := degreeFourierLocalError A q t
  have hprod : centeredDegreeFourierReal A q t =
      Complex.exp (∑ e ∈ A, (L e - ((q e : ℝ) : ℂ) * z e)) := by
    rw [centeredDegreeFourierReal, Complex.exp_sum]
    refine Finset.prod_congr rfl (fun e he ↦ ?_)
    change Complex.exp (-(((q e : ℝ) : ℂ) * z e)) *
      (1 - ((q e : ℝ) : ℂ) + ((q e : ℝ) : ℂ) * Complex.exp (z e)) =
      Complex.exp (L e - ((q e : ℝ) : ℂ) * z e)
    rw [Complex.exp_sub]
    have h : Complex.exp (L e) =
        1 - ((q e : ℝ) : ℂ) + ((q e : ℝ) : ℂ) * Complex.exp (z e) :=
      Complex.exp_log (edgeLogFactor_ne_zero (q e) (s e) (ht e he))
    rw [h, Complex.exp_neg, div_eq_mul_inv, mul_comm]
  have hquad : g = ∑ e ∈ A, w e * s e ^ 2 := by
    rw [← degreeCovariance_quadratic]
    simp only [g, Q, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hp (e : Edge (Fin n)) : L e - ((q e : ℝ) : ℂ) * z e =
      (((-w e * s e ^ 2 / 2 + degreeQuarticCoefficient (q e) * s e ^ 4 : ℝ) : ℂ)) +
      ((degreeCubicCoefficient (q e) * s e ^ 3 : ℝ) : ℂ) * Complex.I +
      (L e - P e) := by
    have h := bernoulliCumulantPolynomial_imaginary (q e : ℝ) (s e)
    change P e - (q e : ℝ) * z e = _ at h
    dsimp only [z, w, degreeQuarticCoefficient, degreeCubicCoefficient] at *
    push_cast at *
    linear_combination h
  have hsum : (∑ e ∈ A, (L e - ((q e : ℝ) : ℂ) * z e)) =
      (((-g / 2 + H : ℝ) : ℂ) + (F : ℂ) * Complex.I + R) := by
    simp_rw [hp]
    rw [hquad]
    dsimp only [H, F, R, degreeFourierLocalError, L, P, z, s]
    push_cast
    simp only [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_neg_distrib,
      ← Finset.sum_mul, neg_mul, Complex.ofReal_mul, Complex.ofReal_pow]
  change centeredDegreeFourierReal A q t =
    Real.exp (-g / 2) • (realCharacter 1 F * (Real.exp H : ℂ) * Complex.exp R)
  rw [hprod, hsum]
  simp only [realCharacter, one_mul, Complex.ofReal_add, Complex.exp_add,
    Complex.ofReal_exp, Complex.real_smul]
  ring

/-- Gaussian representation on the real small box with arbitrary available edges. -/
theorem centeredRealPeak_eq_gaussian {n : ℕ}
    (A : Finset (Edge (Fin n))) (q : Edge (Fin n) → Icc (0 : ℝ) 1)
    (hQ : (degreeCovariance A q).PosDef) {r : ℝ} (hr : 2 * r ≤ 1 / 4) :
    let Q := degreeCovariance A q
    let B := (CFC.sqrt Q)⁻¹
    let U := phaseGaussianBox Q r
    centeredRealPeak A q r = (phaseGaussianScale Q : ℂ) *
      ∫ x, U.indicator (fun y ↦ realCharacter 1 (phaseGaussianCubic A q y) *
        (Real.exp (phaseGaussianQuartic A q y) : ℂ) *
        Complex.exp (degreeFourierLocalError A q (B *ᵥ y))) x ∂standardGaussianProduct n := by
  let Q := degreeCovariance A q
  let B := (CFC.sqrt Q)⁻¹
  let F := edgeCubic A (fun e ↦ degreeCubicCoefficient (q e))
  let H := edgeQuartic A (fun e ↦ degreeQuarticCoefficient (q e))
  let R := degreeFourierLocalError A q
  let U := realPhaseBox (α := Fin n) r
  let W (t : Fin n → ℝ) := realCharacter 1 (F t) * (Real.exp (H t) : ℂ) * Complex.exp (R t)
  let L (t : Fin n → ℝ) := Real.exp (-(t ⬝ᵥ (Q *ᵥ t)) / 2)
  have hU : MeasurableSet U := by
    rw [show U = ⋂ i, {x : Fin n → ℝ | |x i| ≤ r} by ext x; simp [U, realPhaseBox]]
    exact MeasurableSet.iInter (fun i ↦ measurableSet_le
      (continuous_abs.measurable.comp (measurable_pi_apply i)) measurable_const)
  have hcontF : Continuous F := by
    unfold F edgeCubic
    apply continuous_finsetSum
    intro e _
    fun_prop
  have hcontH : Continuous H := by
    unfold H edgeQuartic
    apply continuous_finsetSum
    intro e _
    fun_prop
  have hW : StronglyMeasurable W :=
    (((continuous_realCharacter 1).comp hcontF).measurable.mul
      ((Complex.continuous_ofReal.comp Real.continuous_exp).comp hcontH).measurable).mul
      (Complex.continuous_exp.measurable.comp (measurable_degreeFourierLocalError A q))
      |>.stronglyMeasurable
  have hlocal : (∫ t in U, centeredDegreeFourierReal A q t) = ∫ t, L t • U.indicator W t := by
    rw [← integral_indicator hU]
    apply integral_congr_ae
    refine ae_of_all _ (fun t ↦ ?_)
    change U.indicator (centeredDegreeFourierReal A q) t = L t • U.indicator W t
    by_cases ht : t ∈ U
    · rw [indicator_of_mem ht, indicator_of_mem ht]
      refine centeredDegreeFourierReal_expansion A q t (fun e _ ↦ ?_)
      exact (abs_add_le _ _).trans (by linarith only [ht e.val.1, ht e.val.2, hr])
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
  have hchange := integral_quadratic_smul_eq_gaussianProduct Q hQ (U.indicator W) (hW.indicator hU)
  change (∫ t, L t • U.indicator W t) =
    ((Real.sqrt (2 * Real.pi)) ^ n / Real.sqrt Q.det) •
      ∫ x, U.indicator W (B *ᵥ x) ∂standardGaussianProduct n at hchange
  have hpre (x : Fin n → ℝ) :
      U.indicator W (B *ᵥ x) = (phaseGaussianBox Q r).indicator (W ∘ B.mulVec) x := by
    by_cases h : B *ᵥ x ∈ U
    · rw [indicator_of_mem h, indicator_of_mem (show x ∈ phaseGaussianBox Q r from h)]
      rfl
    · rw [indicator_of_notMem h, indicator_of_notMem (show x ∉ phaseGaussianBox Q r from h)]
  simp_rw [hpre] at hchange
  change (((2 * Real.pi) ^ n : ℝ) : ℂ)⁻¹ * (∫ t in U, centeredDegreeFourierReal A q t) =
    (phaseGaussianScale Q : ℂ) * ∫ x, (phaseGaussianBox Q r).indicator (W ∘ B.mulVec) x
      ∂standardGaussianProduct n
  rw [hlocal, hchange]
  let c := (Real.sqrt (2 * Real.pi)) ^ n / Real.sqrt Q.det
  let s : ℝ := (2 * Real.pi) ^ n
  let J := ∫ x, (phaseGaussianBox Q r).indicator (W ∘ B.mulVec) x ∂standardGaussianProduct n
  change (s : ℂ)⁻¹ * (c • J) = ((c / s : ℝ) : ℂ) * J
  calc
    _ = ((c : ℂ) / (s : ℂ)) * J := by
      rw [Complex.real_smul, div_eq_mul_inv, ← mul_assoc,
        mul_comm ((s : ℂ)⁻¹) (c : ℂ)]
    _ = _ := congrArg (· * J) (Complex.ofReal_div c s).symm

/-- The cubic estimate and first expansion of (A.3) for available-edge
arrays satisfying the linear covariance and inverse-row bounds. -/
theorem eventually_centeredRealPeak_sub_le_uniform {l a C : ℝ}
    (hl : 0 < l) (ha : 0 < a) (hC : 0 < C) :
    ∃ U V M : ℝ, 0 < U ∧ 0 < V ∧ 0 ≤ M ∧ ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ (A : Finset (Edge (Fin n))) (q : Edge (Fin n) → Icc (0 : ℝ) 1),
        (∀ e ∈ A, l ≤ (q e : ℝ) * (1 - q e)) →
        let Q := degreeCovariance A q
        Q.PosDef →
        (∀ x : Fin n → ℝ, a * (n : ℝ) * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (Q *ᵥ x)) →
        (∀ i, (∑ j, |Q⁻¹ i j|) ≤ C / (n : ℝ)) →
        let Ξ := phaseGaussianScale Q
        let μ := phaseGaussianCubicSecondMoment A q
        let ν := phaseGaussianQuarticMean A q
        0 ≤ μ ∧ μ ≤ U ∧ |ν| ≤ M ∧
          ‖(∫ x, realCharacter 1 (phaseGaussianCubic A q x) ∂standardGaussianProduct n) -
            (Real.exp (-μ / 2) : ℂ)‖ ≤ V / Real.sqrt (n : ℝ) ∧
          ‖centeredRealPeak A q (fourierBoxRadius n) -
            ((Ξ * Real.exp (-μ / 2 + ν) : ℝ) : ℂ)‖ ≤ ε * Ξ := by
  obtain ⟨U, V, hU, hV, hCubic⟩ :=
    gaussianCubic_character_uniform_of_inverse_rows hl (K := 1 / 24) (by norm_num) hC
  obtain ⟨M, hM, hQuartic⟩ := eventually_gaussian_quartic_box_weight_sub_le
    (a := a⁻¹) (K := 1 / 96) (by positivity) (by norm_num)
  refine ⟨U, V, M, hU, hV, hM, ?_⟩
  intro ε hε
  let z := min 1 (ε / (4 * (Real.exp M + 1)))
  have hz₀ : 0 < z := lt_min zero_lt_one (by positivity)
  have hz₁ : z ≤ 1 := min_le_left _ _
  have hzε : z ≤ ε / (4 * (Real.exp M + 1)) := min_le_right _ _
  have hs : Tendsto (fun n : ℕ ↦ V / Real.sqrt n) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := V)).mul (tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)))
    simpa only [div_eq_mul_inv, Function.comp_apply, mul_zero] using h
  filter_upwards [hQuartic z hz₀, eventually_degreeFourierLocalError_le hz₀,
    hs.eventually_lt_const hz₀, eventually_ge_atTop (1 : ℕ)] with n h₄ hR hV' hn
  intro A q hq Q hQ hQuad hrow
  let B := (CFC.sqrt Q)⁻¹
  let b (e : Edge (Fin n)) := degreeQuarticCoefficient (q e)
  let f (e : Edge (Fin n)) := degreeCubicCoefficient (q e)
  let r := fourierBoxRadius n
  let γ := standardGaussianProduct n
  let μ := phaseGaussianCubicSecondMoment A q
  let ν := phaseGaussianQuarticMean A q
  let Ξ := phaseGaussianScale Q
  have hn₀ : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn₀
  obtain ⟨hB, hRows⟩ := gaussian_inverse_sqrt_bounds Q hQ (mul_pos ha hn') hQuad
  have he : (a * (n : ℝ))⁻¹ = a⁻¹ / (n : ℝ) := by field_simp [ha.ne', hn'.ne']
  simp only [he] at hB hRows
  obtain ⟨hν, h₄'⟩ := h₄ A b B (fun e _ ↦ abs_degreeQuarticCoefficient_le (q e)) hRows hB
  have heval (x : Fin n → ℝ) :
      MvPolynomial.eval x (gaussianCubicPolynomial A f (fun e ↦ B *ᵥ realIncidence e)) =
        phaseGaussianCubic A q x := by
    rw [eval_gaussianCubicPolynomial]
    change _ = ∑ e ∈ A, f e * ((B *ᵥ x) e.val.1 + (B *ᵥ x) e.val.2) ^ 3
    exact Finset.sum_congr rfl (fun e _ ↦ by rw [dotProduct_gaussian_whitened_edge Q])
  have h₃ := hCubic n hn₀ A q f hq (fun e _ ↦ abs_degreeCubicCoefficient_le (q e)) hQ hrow
  let G := gaussianCubicPolynomial A f (fun e ↦ B *ᵥ realIncidence e)
  let σ := ∫ x, MvPolynomial.eval x G ^ 2 ∂γ
  change 0 ≤ σ ∧ σ ≤ U ∧ ‖(∫ x, realCharacter 1 (MvPolynomial.eval x G) ∂γ) -
    (Real.exp (-σ / 2) : ℂ)‖ ≤ V / Real.sqrt (n : ℝ) at h₃
  dsimp only [σ, G] at h₃
  simp_rw [heval] at h₃
  have hc : ‖(∫ x, realCharacter 1 (phaseGaussianCubic A q x) ∂γ) -
      (Real.exp (-μ / 2) : ℂ)‖ ≤ V / Real.sqrt (n : ℝ) := h₃.2.2
  have h := norm_gaussian_peak_sub_le A q hQ hR.1 hz₀.le hz₁
    (hR.2.2 A q) hν h₄' (hc.trans hV'.le) _ (centeredRealPeak_eq_gaussian A q hQ hR.2.1)
  refine ⟨h₃.1, h₃.2.1, hν, hc, h.trans ?_⟩
  have hΞ : 0 ≤ Ξ := by dsimp only [Ξ, Q]; rw [phaseGaussianScale_eq _ hQ]; positivity
  change Ξ * _ ≤ ε * Ξ
  rw [mul_comm ε Ξ]
  apply mul_le_mul_of_nonneg_left _ hΞ
  have h₁ := mul_le_mul_of_nonneg_left hz₁ (show (0 : ℝ) ≤ 2 * z by positivity)
  have h₂ := (le_div_iff₀ (show 0 < 4 * (Real.exp M + 1) by positivity)).mp hzε
  nlinarith only [h₁, h₂, mul_nonneg hz₀.le (Real.exp_nonneg M)]

/-- Uniform linear covariance and inverse-row bounds after a clique deletion. -/
theorem eventually_overlap_covariance_and_row_bounds {l τ : ℝ} (hl : 0 < l) (hτ : 0 < τ) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (S : Finset (Fin n)) (q : Edge (Fin n) → Icc (0 : ℝ) 1),
        τ * (n : ℝ) ≤ (((Finset.univ : Finset (Fin n)) \ S).card : ℝ) →
        (∀ e, l ≤ (q e : ℝ) * (1 - q e)) →
        let Q := degreeCovariance (edgesOutsideOverlap S) q
        Q.PosDef ∧
        (∀ x : Fin n → ℝ, a * (n : ℝ) * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (Q *ᵥ x)) ∧
        (∀ i, (∑ j, |Q⁻¹ i j|) ≤ C / (n : ℝ)) := by
  let a := l * τ ^ 2 / 3
  let C := a⁻¹ + (1 / 4 : ℝ) / a ^ 2 + (1 / 4 : ℝ) ^ 2 / a ^ 3
  have ha : 0 < a := by dsimp only [a]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨a, C, ha, hC, ?_⟩
  have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hN : ∀ᶠ n : ℕ in atTop, 3 / τ ≤ (n : ℝ) := (tendsto_atTop.1 hnat) _
  filter_upwards [hN, eventually_ge_atTop (1 : ℕ)] with n hN hn
  intro S q hsize hq
  let A := edgesOutsideOverlap S
  let Q := degreeCovariance A q
  let k : ℝ := n
  let m : ℕ := ((Finset.univ : Finset (Fin n)) \ S).card
  let c := a * k
  let r := (1 / 4 : ℝ) / c ^ 2 + k * (1 / 4 : ℝ) ^ 2 / c ^ 3
  have hn₀ : 0 < n := by omega
  have hk : 0 < k := by change 0 < (n : ℝ); exact_mod_cast hn₀
  have hc : 0 < c := mul_pos ha hk
  have hm' : (3 : ℝ) ≤ (m : ℝ) := by
    have h : (3 : ℝ) ≤ (n : ℝ) * τ := (div_le_iff₀ hτ).mp hN
    rw [mul_comm] at h
    exact h.trans hsize
  have hm : 3 ≤ m := by exact_mod_cast hm'
  have hlin : c ≤ l * ((m : ℝ) ^ 2 / (3 * k)) := by
    have h := pow_le_pow_left₀ (show 0 ≤ τ * k by positivity)
      (show τ * k ≤ (m : ℝ) from hsize) 2
    calc
      c = l * ((τ * k) ^ 2 / (3 * k)) := by
        dsimp only [c, a]
        field_simp [hk.ne']
        <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h (by positivity)) hl.le
  have hQuad (x : Fin n → ℝ) : c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (Q *ᵥ x) := by
    have h := (degreeCovariance_outside_overlap_bounds S hm q l hl.le hq x).1
    simp only [Fintype.card_fin] at h
    rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
    refine (mul_le_mul_of_nonneg_right hlin (Finset.sum_nonneg (fun i _ ↦ sq_nonneg (x i)))).trans ?_
    simpa only [Q, A, k, m] using h
  have hHerm : Q.IsHermitian := by
    ext i j
    simp only [Q, degreeCovariance, conjTranspose_apply, star_trivial]
    exact Finset.sum_congr rfl (fun e _ ↦ by ring)
  have hQ : Q.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hHerm
    intro x hx
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      contrapose! hx
      exact funext hx
    have hs : 0 < ∑ i, x i ^ 2 := Finset.sum_pos' (fun _ _ ↦ sq_nonneg _)
      ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
    rw [star_trivial]
    exact (mul_pos hc hs).trans_le (hQuad x)
  obtain ⟨hdiag, hoff⟩ := inverse_entry_bounds Q hc (by norm_num : 0 ≤ (1 / 4 : ℝ)) hQuad
    (fun _ _ hij ↦ degreeCovariance_offDiag_le _ q hij)
  refine ⟨hQ, hQuad, ?_⟩
  intro i
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  rw [← Finset.sum_erase_add Finset.univ (fun j ↦ |Q⁻¹ i j|) (Finset.mem_univ i)]
  calc
    _ ≤ (∑ _ ∈ Finset.univ.erase i, r) + c⁻¹ := by
      apply add_le_add _ (hdiag i)
      apply Finset.sum_le_sum
      intro j hj
      simpa only [Fintype.card_fin, r, k] using hoff i j (Ne.symm (Finset.ne_of_mem_erase hj))
    _ ≤ k * r + c⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hk' : ((Finset.univ.erase i).card : ℝ) ≤ k := by
        change _ ≤ (n : ℝ)
        exact_mod_cast (Finset.card_le_univ (Finset.univ.erase i)).trans_eq (Fintype.card_fin n)
      exact add_le_add (mul_le_mul_of_nonneg_right hk' hr) le_rfl
    _ = C / k := by
      dsimp only [r, c, C]
      field_simp [ha.ne', hk.ne']
      <;> ring

/-- The complex small-box expansion uniformly after any permitted clique
deletion, including the empty deletion and nonintegral degree means. -/
theorem eventually_centeredRealPeak_sub_le_outside_overlap {l τ : ℝ}
    (hl : 0 < l) (hτ : 0 < τ) :
    ∃ U V M : ℝ, 0 < U ∧ 0 < V ∧ 0 ≤ M ∧ ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ (S : Finset (Fin n)) (q : Edge (Fin n) → Icc (0 : ℝ) 1),
        τ * (n : ℝ) ≤ (((Finset.univ : Finset (Fin n)) \ S).card : ℝ) →
        (∀ e, l ≤ (q e : ℝ) * (1 - q e)) →
        let A := edgesOutsideOverlap S
        let Q := degreeCovariance A q
        let Ξ := phaseGaussianScale Q
        let μ := phaseGaussianCubicSecondMoment A q
        let ν := phaseGaussianQuarticMean A q
        0 ≤ μ ∧ μ ≤ U ∧ |ν| ≤ M ∧
          ‖(∫ x, realCharacter 1 (phaseGaussianCubic A q x) ∂standardGaussianProduct n) -
            (Real.exp (-μ / 2) : ℂ)‖ ≤ V / Real.sqrt (n : ℝ) ∧
          ‖centeredRealPeak A q (fourierBoxRadius n) -
            ((Ξ * Real.exp (-μ / 2 + ν) : ℝ) : ℂ)‖ ≤ ε * Ξ := by
  obtain ⟨a, C, ha, hC, hgeom⟩ := eventually_overlap_covariance_and_row_bounds hl hτ
  obtain ⟨U, V, M, hU, hV, hM, hpeak⟩ := eventually_centeredRealPeak_sub_le_uniform hl ha hC
  refine ⟨U, V, M, hU, hV, hM, fun ε hε ↦ ?_⟩
  filter_upwards [hgeom, hpeak ε hε] with n hg hp
  intro S q hsize hq
  obtain ⟨hQ, hQuad, hrow⟩ := hg S q hsize hq
  exact hp (edgesOutsideOverlap S) q (fun e _ ↦ hq e) hQ hQuad hrow

/-- Lemma A.2 for arbitrary bounded cubic coefficients on the remaining edges. -/
theorem eventually_gaussianCubic_outside_overlap_uniform {l τ K : ℝ}
    (hl : 0 < l) (hτ : 0 < τ) (hK : 0 < K) :
    ∃ U V : ℝ, 0 < U ∧ 0 < V ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (S : Finset (Fin n))
        (q : Edge (Fin n) → Icc (0 : ℝ) 1) (a : Edge (Fin n) → ℝ),
        τ * (n : ℝ) ≤ (((Finset.univ : Finset (Fin n)) \ S).card : ℝ) →
        (∀ e, l ≤ (q e : ℝ) * (1 - q e)) →
        let A := edgesOutsideOverlap S
        (∀ e ∈ A, |a e| ≤ K) →
        let Q := degreeCovariance A q
        let v (e : Edge (Fin n)) := (CFC.sqrt Q)⁻¹ *ᵥ realIncidence e
        let F := gaussianCubicPolynomial A a v
        let γ := standardGaussianProduct n
        let μ := ∫ x, MvPolynomial.eval x F ^ 2 ∂γ
        0 ≤ μ ∧ μ ≤ U ∧
          ‖(∫ x, realCharacter 1 (MvPolynomial.eval x F) ∂γ) -
            (Real.exp (-μ / 2) : ℂ)‖ ≤ V / Real.sqrt (n : ℝ) := by
  obtain ⟨a, C, ha, hC, hgeom⟩ := eventually_overlap_covariance_and_row_bounds hl hτ
  obtain ⟨U, V, hU, hV, hcubic⟩ := gaussianCubic_character_uniform_of_inverse_rows hl hK hC
  refine ⟨U, V, hU, hV, ?_⟩
  filter_upwards [hgeom, eventually_ge_atTop (1 : ℕ)] with n hg hn
  intro S q a hsize hq A habs
  obtain ⟨hQ, _, hrow⟩ := hg S q hsize hq
  exact hcubic n (by omega) A q a (fun e _ ↦ hq e) habs hQ hrow

end BoundedEdgeRegularSubgraphs
