module

public import BoundedEdgeRegularSubgraphs.FourierCenteredPeak
public import BoundedEdgeRegularSubgraphs.ResidualLocalLimit
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Theorem B.2: the centred degree atom
-/

public section

open Filter MeasureTheory Matrix Set
open scoped BigOperators MatrixOrder

namespace BoundedEdgeRegularSubgraphs

private theorem edgesOutsideOverlap_empty {n : ℕ} :
    edgesOutsideOverlap (∅ : Finset (Fin n)) = Finset.univ := by
  ext e
  simp [edgesOutsideOverlap]

/-- The centred atom has the asymptotic with uniform relative error and
the exponential lower bound in Theorem B.2. -/
theorem centered_degreeAtom_uniform_asymptotic_of_variance_floor {l : ℝ} (hl : 0 < l) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      ∀ (q : Edge (Fin k) → Icc (0 : ℝ) 1) (d : Fin k → ℤ),
        (∀ e, l ≤ (q e : ℝ) * (1 - q e)) →
        (∀ i, (d i : ℝ) = degreeSum (fun e ↦ (q e : ℝ)) i) → Even (∑ i, d i) →
        let A : Finset (Edge (Fin k)) := Finset.univ
        let μ := phaseGaussianCubicSecondMoment A q
        let ν := phaseGaussianQuarticMean A q
        let N := (Real.sqrt (2 * Real.pi)) ^ k * Real.sqrt (degreeCovariance A q).det
        let p := (graphLaw q).real (degreeAtom A d)
        let p₀ := (2 * Real.exp (-μ / 2 + ν)) / N
        |p - p₀| ≤ ε * p₀ ∧ c / N ≤ p ∧
          Real.exp (-(k : ℝ) / 2 * Real.log k - C * k) ≤ p := by
  obtain ⟨U, M, hU, hM, hPk⟩ := eventually_centered_peak_sub_le_uniform hl
  let c := Real.exp (-U / 2 - M)
  let C := Real.log Real.pi / 2 + |Real.log c|
  have hc : 0 < c := Real.exp_pos _
  have hC : 0 < C := add_pos_of_pos_of_nonneg
    (div_pos (Real.log_pos (by linarith only [Real.pi_gt_three])) (by norm_num)) (abs_nonneg _)
  refine ⟨c, C, hc, hC, ?_⟩
  intro ε hε
  let z := min 1 ε * c / 3
  have hz : 0 < z := div_pos (mul_pos (lt_min zero_lt_one hε) hc) (by norm_num)
  have hB := eventually_integral_degreeFourier_outside_small_boxes_le_uniform hl
    (τ := 1 / 2) (by norm_num) hz
  filter_upwards [hPk z hz, hB, eventually_ge_atTop (3 : ℕ),
    eventually_degreeFourierLocalError_le_one] with k hP hTail hk hR
  intro q d hq hd hEven
  let A : Finset (Edge (Fin k)) := Finset.univ
  let Q := degreeCovariance A q
  let Ξ := phaseGaussianScale Q
  let N := (Real.sqrt (2 * Real.pi)) ^ k * Real.sqrt Q.det
  let μ := phaseGaussianCubicSecondMoment A q
  let ν := phaseGaussianQuarticMean A q
  let s := Real.exp (-μ / 2 + ν)
  let p := (graphLaw q).real (degreeAtom A d)
  let r := fourierBoxRadius k
  let P := ∫ t in phaseBox (0 : PhaseCircle) r, degreeFourier A q d t ∂phaseLaw
  let T := ∫ t in (phaseBox (0 : PhaseCircle) r ∪ phaseBox (Real.pi : PhaseCircle) r)ᶜ,
    degreeFourier A q d t ∂phaseLaw
  obtain ⟨hQ, _⟩ := full_degreeCovariance_posDef_of_floor hk q hl hq
  have hNorm : Ξ = 1 / N := phaseGaussianScale_eq Q hQ
  have hΞ : 0 ≤ Ξ := by rw [hNorm]; dsimp only [N]; positivity
  have hr : r < Real.pi / 2 := by
    dsimp only [r]
    linarith only [hR.2.1, Real.pi_gt_three]
  let _ : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hSplit : (p : ℂ) = 2 * P + T := probability_degreeAtom_eq_twice_peak_add_tail A q d hEven hr
  obtain ⟨_, hμ, hν, hPeak⟩ := hP q d hq hd
  have hs : c ≤ s := Real.exp_le_exp.mpr (by
    change -U / 2 - M ≤ -μ / 2 + ν
    linarith only [hμ, (abs_le.mp hν).1])
  have hs₀ : 0 < s := Real.exp_pos _
  have hS : (1 / 2 : ℝ) * k ≤ (((Finset.univ : Finset (Fin k)) \ (∅ : Finset (Fin k))).card : ℝ) := by
    rw [Finset.sdiff_empty, Finset.card_univ, Fintype.card_fin]
    linarith only [show 0 ≤ (k : ℝ) by positivity]
  have hT := hTail ∅ q d hS hq
  dsimp only at hT
  rw [edgesOutsideOverlap_empty] at hT
  have hT' : ‖T‖ ≤ z * Ξ := (norm_integral_le_integral_norm _).trans hT
  have hcplx : ‖(p : ℂ) - 2 * ((Ξ * s : ℝ) : ℂ)‖ ≤ 3 * z * Ξ := by
    rw [hSplit, show 2 * P + T - 2 * ((Ξ * s : ℝ) : ℂ) =
      2 * (P - ((Ξ * s : ℝ) : ℂ)) + T by ring]
    have h := norm_add_le (2 * (P - ((Ξ * s : ℝ) : ℂ))) T
    rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num] at h
    have hh : 2 * ‖P - ((Ξ * s : ℝ) : ℂ)‖ ≤ 2 * (z * Ξ) :=
      mul_le_mul_of_nonneg_left hPeak (by norm_num)
    linarith only [h, hh, hT']
  have hreal : |p - (2 * s) * Ξ| ≤ 3 * z * Ξ := by
    rw [show (p : ℂ) - 2 * ((Ξ * s : ℝ) : ℂ) = ((p - (2 * s) * Ξ : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs] at hcplx
    exact hcplx
  have hz₁ : 3 * z ≤ c := by
    have h := mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) ε) hc.le
    dsimp only [z]
    linarith only [h]
  have hzε : 3 * z ≤ ε * c := by
    have h := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) ε) hc.le
    dsimp only [z]
    linarith only [h]
  have hrelative : |p - (2 * s) * Ξ| ≤ ε * ((2 * s) * Ξ) := by
    refine hreal.trans ?_
    have h := mul_le_mul_of_nonneg_left (show c ≤ 2 * s by linarith only [hs, hs₀.le]) hε.le
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hzε.trans h) hΞ
  have hlower : c * Ξ ≤ p := by
    have hh := mul_le_mul_of_nonneg_right hz₁ hΞ
    have hs' := mul_le_mul_of_nonneg_right hs hΞ
    linarith only [(abs_le.mp hreal).1, hh, hs']
  rw [hNorm, mul_one_div] at hrelative hlower
  refine ⟨hrelative, hlower, ?_⟩
  have hD := degreeCovariance_outside_overlap_det_le (∅ : Finset (Fin k))
    (by simpa only [Finset.sdiff_empty, Finset.card_univ, Fintype.card_fin] using hk) q
  rw [edgesOutsideOverlap_empty, Fintype.card_fin] at hD
  have hdet : Q.det ≤ ((k : ℝ) / 2) ^ k := by
    have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    exact hD.trans (pow_le_pow_left₀ (by linarith only [hk₁]) (by linarith) k)
  exact (exp_le_gaussian_atom_normalizer (show 1 ≤ k by omega) hQ.det_pos hc hdet).trans hlower

end BoundedEdgeRegularSubgraphs
