module

public import BoundedEdgeRegularSubgraphs.FourierSmallBoxBound
public import BoundedEdgeRegularSubgraphs.FourierTailAssembly
import Mathlib.Tactic

/-!
# The finite residual-atom estimate
-/

public section

open MeasureTheory Matrix Set
open scoped BigOperators MatrixOrder

namespace BoundedEdgeRegularSubgraphs

private theorem integral_phase_norm_pi_box_eq_zero {n : ℕ}
    (A : Finset (Edge (Fin (n + 1)))) (q : Edge (Fin (n + 1)) → Icc (0 : ℝ) 1)
    (d : Fin (n + 1) → ℤ) (r : ℝ) :
    (∫ t in phaseBox (Real.pi : PhaseCircle) r, ‖degreeFourier A q d t‖ ∂phaseLaw) =
      ∫ t in phaseBox 0 r, ‖degreeFourier A q d t‖ ∂phaseLaw := by
  have hempty (b : PhaseCircle) : phaseBox (α := Fin (n + 1)) b (-1) = ∅ := by
    ext t
    simp only [mem_empty_iff_false, iff_false]
    intro ht
    linarith only [show ‖t 0 - b‖ ≤ -1 from ht 0, norm_nonneg (t 0 - b)]
  simpa only [hempty, sdiff_empty] using integral_phase_annulus_pi_eq_zero A q d r (-1)

/-- The finite residual degree-atom bound obtained from a small-box
estimate and the two tail estimates, for arbitrary target vectors. -/
theorem probability_residual_degreeAtom_le_of_fourier_rates {n : ℕ}
    (S : Finset (Fin (n + 1))) (hm : 3 ≤ ((Finset.univ : Finset (Fin (n + 1))) \ S).card)
    (q : Edge (Fin (n + 1)) → Icc (0 : ℝ) 1) (d : Fin (n + 1) → ℤ)
    {l R r ε : ℝ} (hl : 0 < l) (hq : ∀ e, l ≤ (q e : ℝ) * (1 - q e))
    (hR : 2 * R ≤ Real.pi / 3) (hr : 0 ≤ r) (hr' : 2 * r ≤ 1 / 4)
    (hε : ∀ x ∈ realPhaseBox (α := Fin (n + 1)) r,
      ‖degreeFourierLocalError (edgesOutsideOverlap S) q x‖ ≤ ε)
    {a₀ a : ℝ} (ha : 0 ≤ a)
    (hsmall :
      let lower := l * ((((Finset.univ : Finset (Fin (n + 1))) \ S).card : ℝ) ^ 2 / (3 * (n + 1 : ℝ)))
      a + 2 * (n + 1) * Real.exp (-(lower / 2) * r ^ 2 / 2) ≤ 1 / 2)
    (hT : (∫ t in (phaseBox (0 : PhaseCircle) R ∪ phaseBox (Real.pi : PhaseCircle) R)ᶜ,
      ‖degreeFourier (edgesOutsideOverlap S) q d t‖ ∂phaseLaw) ≤
        a₀ + a * ∫ t, ‖degreeFourier (edgesOutsideOverlap S) q d t‖ ∂phaseLaw) :
    let A := edgesOutsideOverlap S
    let Q := degreeCovariance A q
    let lower := l * ((((Finset.univ : Finset (Fin (n + 1))) \ S).card : ℝ) ^ 2 / (3 * (n + 1 : ℝ)))
    let K := (1 / 96 : ℝ)
    let κ := 4 * (2 * r) ^ 3 * K * (((n + 1 : ℕ) : ℝ) - 1) * Real.sqrt (n + 1 : ℕ) * Real.sqrt lower⁻¹
    let C := Real.exp (ε + 24 * K * (((n + 1 : ℕ) : ℝ) - 1) * (n + 1 : ℕ) * lower⁻¹ ^ 2 + κ ^ 2 / 2)
    (graphLaw q).real (degreeAtom A d) ≤ 4 * C * phaseGaussianScale Q + 2 * a₀ := by
  let k : ℕ := n + 1
  let A := edgesOutsideOverlap S
  let Q := degreeCovariance A q
  let m := ((Finset.univ : Finset (Fin k)) \ S).card
  let lower := l * ((m : ℝ) ^ 2 / (3 * (n + 1 : ℝ)))
  let K := (1 / 96 : ℝ)
  let κ := 4 * (2 * r) ^ 3 * K * ((k : ℝ) - 1) * Real.sqrt k * Real.sqrt lower⁻¹
  let C := Real.exp (ε + 24 * K * ((k : ℝ) - 1) * k * lower⁻¹ ^ 2 + κ ^ 2 / 2)
  let U := phaseBox (α := Fin k) (0 : PhaseCircle) r ∪ phaseBox (Real.pi : PhaseCircle) r
  let f (t : Fin k → PhaseCircle) := ‖degreeFourier A q d t‖
  let Ξ := phaseGaussianScale Q
  have hm' : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hlow : 0 < lower := by dsimp only [lower]; positivity
  have hquad (x : Fin k → ℝ) : lower * ∑ i, x i ^ 2 ≤ x ⬝ᵥ (Q *ᵥ x) := by
    have h := (degreeCovariance_outside_overlap_bounds S hm q l hl.le hq x).1
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, lower, m, dotProduct, Matrix.mulVec,
      Finset.mul_sum, mul_assoc, Q, A]
      using h
  have hQa : Q.IsHermitian := by
    ext i j
    simp only [conjTranspose_apply, star_trivial, Q, degreeCovariance]
    exact Finset.sum_congr rfl (fun e _ ↦ by ring)
  have hQ : Q.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hQa
    intro v hv
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      contrapose! hv
      exact funext hv
    have hs : 0 < ∑ i, v i ^ 2 := Finset.sum_pos' (fun _ _ ↦ sq_nonneg _)
      ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
    rw [star_trivial]
    exact (mul_pos hlow hs).trans_le (hquad v)
  have hin : Integrable f phaseLaw := (integrable_degreeFourier A q d).norm
  have hn : ∀ t, 0 ≤ f t := fun _ ↦ norm_nonneg _
  have h₀ : (∫ t in phaseBox 0 r, f t ∂phaseLaw) ≤ C * Ξ :=
    integral_degreeFourier_smallBox_le_exp_of_covariance_lower (Nat.succ_pos n) A q d hQ hlow hquad hr hr' hε
  have hπ : (∫ t in phaseBox (Real.pi : PhaseCircle) r, f t ∂phaseLaw) =
      ∫ t in phaseBox 0 r, f t ∂phaseLaw := integral_phase_norm_pi_box_eq_zero A q d r
  have hU : MeasurableSet U := (measurableSet_phaseBox _ _).union (measurableSet_phaseBox _ _)
  have hP : (∫ t in U, f t ∂phaseLaw) ≤ (2 * C) * Ξ := by
    let C₀ := phaseBox (α := Fin k) (0 : PhaseCircle) r
    let C₁ := phaseBox (α := Fin k) (Real.pi : PhaseCircle) r
    have h₀i : Integrable f (phaseLaw.restrict C₀) := hin.integrableOn
    have h₁i : Integrable f (phaseLaw.restrict C₁) := hin.integrableOn
    have h := integral_mono_measure (Measure.restrict_union_le (μ := phaseLaw) C₀ C₁)
      (ae_of_all _ hn) (h₀i.add_measure h₁i)
    rw [integral_add_measure h₀i h₁i] at h
    change (∫ t in U, f t ∂phaseLaw) ≤ (∫ t in phaseBox 0 r, f t ∂phaseLaw) +
      ∫ t in phaseBox (Real.pi : PhaseCircle) r, f t ∂phaseLaw at h
    rw [hπ] at h
    linarith only [h, h₀]
  have hcurv : lower / 2 ≤
      l * ((m : ℝ) ^ 2 / (3 * Fintype.card (Fin k))) / 2 := by
    simp only [lower, Fintype.card_fin, k, Nat.cast_add, Nat.cast_one, le_refl]
  have hsmall' : a + 2 * (n + 1 : ℝ) * Real.exp (-(lower / 2) * r ^ 2 / 2) ≤ 1 / 2 := by
    simpa only [lower, m, k, Nat.cast_add, Nat.cast_one] using hsmall
  have htail := integral_degreeFourier_outside_small_boxes_le S hm q d hl.le hq
    (div_nonneg hlow.le (by norm_num)) hcurv hR hr ha hsmall' hP hT
  let f₁ := a + 2 * (n + 1 : ℝ) * Real.exp (-(lower / 2) * r ^ 2 / 2)
  have hP₀ : 0 ≤ (∫ t in U, f t ∂phaseLaw) := setIntegral_nonneg_of_ae (ae_of_all _ hn)
  have ha₀ : 0 ≤ a₀ + (2 * C) * Ξ := by
    have hT₀ : 0 ≤ (∫ t in Uᶜ, f t ∂phaseLaw) := setIntegral_nonneg_of_ae (ae_of_all _ hn)
    have h : 0 ≤ f₁ := add_nonneg ha (by positivity)
    change (∫ t in Uᶜ, f t ∂phaseLaw) ≤ a₀ + 2 * f₁ * ((2 * C) * Ξ + a₀) at htail
    by_contra! hn'
    have hbad := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) h)
      (show (2 * C) * Ξ + a₀ ≤ 0 by linarith only [hn'])
    linarith only [hT₀, htail, hbad, hP₀.trans hP, hn']
  have hrest : (∫ t in Uᶜ, f t ∂phaseLaw) ≤ (2 * C) * Ξ + 2 * a₀ := by
    change (∫ t in Uᶜ, f t ∂phaseLaw) ≤ a₀ + 2 * f₁ * ((2 * C) * Ξ + a₀) at htail
    have hhalf : 2 * f₁ ≤ 1 := by dsimp only [f₁]; linarith only [hsmall']
    have hvalue : 0 ≤ (2 * C) * Ξ + a₀ := by linarith only [ha₀]
    have h := mul_le_mul_of_nonneg_right hhalf hvalue
    linarith only [h, htail]
  have htotal := integral_add_compl hU hin
  have hp := congrArg norm (probability_degreeAtom_eq_integral_degreeFourier A q d)
  have hprob : 0 ≤ (graphLaw q).real (degreeAtom A d) := ENNReal.toReal_nonneg
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hprob] at hp
  have hf := norm_integral_le_integral_norm (μ := phaseLaw) (degreeFourier A q d)
  change ‖∫ t, degreeFourier A q d t ∂phaseLaw‖ ≤ ∫ t, f t ∂phaseLaw at hf
  change _ ≤ 4 * C * Ξ + 2 * a₀
  exact (hp.le.trans hf).trans (by linarith only [htotal, hrest, hP])

end BoundedEdgeRegularSubgraphs
