module

public import BoundedEdgeRegularSubgraphs.FourierResidualUpper
public import BoundedEdgeRegularSubgraphs.FourierOuterEnvelope
public import BoundedEdgeRegularSubgraphs.FourierOuterTail
public import BoundedEdgeRegularSubgraphs.FourierUniformBoxCost
public import BoundedEdgeRegularSubgraphs.CovarianceDetBound
public import BoundedEdgeRegularSubgraphs.AtomLowerDeduction
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Proposition C.1: uniform atoms after deleting a clique
-/

public section

open MeasureTheory Matrix Filter Set
open scoped BigOperators MatrixOrder Topology

namespace BoundedEdgeRegularSubgraphs

/-- The uniform residual-atom upper bound and the uniform Fourier tail
with a positive variance floor and a fixed fraction of undeleted vertices. -/
theorem eventually_probability_residual_degreeAtom_and_fourier_tail_le {l τ : ℝ}
    (hl : 0 < l) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      ∀ (S : Finset (Fin k)) (q : Edge (Fin k) → Icc (0 : ℝ) 1) (d : Fin k → ℤ),
        τ * k ≤ (((Finset.univ : Finset (Fin k)) \ S).card : ℝ) →
        (∀ e, l ≤ (q e : ℝ) * (1 - q e)) →
        let A := edgesOutsideOverlap S
        let Ξ := phaseGaussianScale (degreeCovariance A q)
        let r := fourierBoxRadius k
        (graphLaw q).real (degreeAtom A d) ≤
          C / ((Real.sqrt (2 * Real.pi)) ^ k * Real.sqrt (degreeCovariance A q).det) ∧
          (∫ t in (phaseBox (0 : PhaseCircle) r ∪ phaseBox (Real.pi : PhaseCircle) r)ᶜ,
            ‖degreeFourier A q d t‖ ∂phaseLaw) ≤ ε * Ξ := by
  let η := Real.pi / 1200
  let a := l * τ ^ 2 / 3
  let cost := Real.exp (2 + 1 / (4 * a ^ 2))
  have hη : 0 < η := div_pos Real.pi_pos (by norm_num)
  have hηπ : η ≤ Real.pi := by dsimp only [η]; linarith only [Real.pi_pos]
  have ha : 0 < a := by dsimp only [a]; positivity
  obtain ⟨γ, hγ, hγcomp⟩ :=
    phaseBernoulliFactor_compare_exceptional hη (by dsimp only [η]; linarith only [Real.pi_pos]) hl
  let cBad := 2 * l * Real.sin (η / 2) ^ 2
  have hcBad : 0 < cBad := by
    have hs := Real.sin_pos_of_pos_of_lt_pi (show 0 < η / 2 by positivity)
      (show η / 2 < Real.pi by linarith only [hηπ, Real.pi_pos])
    dsimp only [cBad]
    positivity
  let rBig := 10 * η
  have hBig : 2 * rBig ≤ Real.pi / 3 := by dsimp only [rBig, η]; linarith only [Real.pi_pos]
  have hcost₀ : 0 < cost := Real.exp_pos _
  refine ⟨4 * cost + 2, by positivity, ?_⟩
  intro ε hε₀
  let b := min (1 / 4) (ε / (8 * (2 * cost + 1)))
  let c := min 1 (ε / 2)
  have hb₀ : 0 < b := lt_min (by norm_num) (by positivity)
  have hc₀ : 0 < c := lt_min zero_lt_one (by positivity)
  have E₁ := eventually_valid_fourier_cutoffs hτ hη
  have E₂ := (tendsto_fourierOuterEnvelope hη hγ hτ).eventually_lt_const hb₀
  have E₃ : ∀ᶠ k : ℕ in atTop, 2 * k * Real.exp (-(a / 4) * Real.log k ^ 2) < b := by
    have h := (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_nat_mul_exp_neg_log_sq (show 0 < a / 4 by positivity))
    simp only [mul_zero] at h
    filter_upwards [h.eventually_lt_const hb₀] with k hk
    simpa only [mul_assoc] using hk
  have E₄ := eventually_uniform_fourierBox_cost ha
  have E₅ := eventually_degreeFourierLocalError_le_one
  have E₆ := (tendsto_exp_many_bad_normalized (C := Real.log Real.pi / 2) hcBad).eventually_lt_const hc₀
  filter_upwards [eventually_ge_atTop (1 : ℕ), E₁, E₂, E₃, E₄, E₅, E₆] with
    k hk hcut houterRate hannRate hcost hrem hbadRate
  cases k with
  | zero => omega
  | succ n =>
    intro S q d hcount hq
    let k : ℕ := n + 1
    let m := ((Finset.univ : Finset (Fin k)) \ S).card
    let A := edgesOutsideOverlap S
    let Q := degreeCovariance A q
    let Ξ := phaseGaussianScale Q
    let L := fourierExceptionCutoff τ k
    let M := fourierBadCutoff k
    let r := fourierBoxRadius k
    let w := ((k : ℝ) ^ 2)⁻¹
    let u := fourierOuterEnvelope η γ τ L k
    let bad := Real.exp (-cBad * M)
    let lower := l * ((m : ℝ) ^ 2 / (3 * (k : ℝ)))
    let f (t : Fin k → PhaseCircle) := ‖degreeFourier A q d t‖
    have hk₀ : (0 : ℝ) < k := by exact_mod_cast Nat.succ_pos n
    have hmle : m ≤ k := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ ((Finset.univ : Finset (Fin k)) \ S)
    obtain ⟨hwin, hcut'⟩ := hcut
    obtain ⟨hm, hdeg, hpair, hcutCount⟩ := hcut' m hcount hmle
    have hLk : L ≤ k := by
      have hpos : (0 : ℝ) < ((m - L : ℕ) : ℝ) :=
        (show 0 < τ * (k : ℝ) / 2 by positivity).trans_le hcutCount
      have hh : 0 < m - L := by exact_mod_cast hpos
      omega
    have hw : 0 < w := by dsimp only [w]; positivity
    have hwπ : w ≤ Real.pi := by
      have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast Nat.succ_pos n
      have h₁ : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk₁]
      have h₂ := inv_anti₀ zero_lt_one h₁
      norm_num at h₂
      exact h₂.trans (by linarith only [Real.pi_gt_three])
    have hwindow : 0 < η - (L : ℝ) * w := by
      dsimp only [w]
      rw [← div_eq_mul_inv]
      linarith only [hwin, hη]
    have hul : 0 ≤ u := by
      dsimp only [u, fourierOuterEnvelope]
      exact mul_nonneg (div_nonneg (by positivity) hη.le) (by positivity)
    have ho := integral_degreeFourier_outside_fixed_boxes_le S q d M L
      hη hηπ hl.le hγ.le hw hwπ hwindow hq hdeg hpair
      (fun e x y z b hb hx hy hz ↦ hγcomp (q e) x y z b (hq e) hb hx hy hz)
    have ho' : (∫ t in (phaseBox (0 : PhaseCircle) rBig ∪ phaseBox (Real.pi : PhaseCircle) rBig)ᶜ,
        f t ∂phaseLaw) ≤ bad + u * ∫ t, f t ∂phaseLaw := by
      refine ho.trans (add_le_add_right ?_ _)
      have henv := fourier_outer_factor_le_envelope k L m (Nat.succ_pos n) hLk hη hγ.le hcutCount hwin
      have hc : k - S.card = m := by
        dsimp only [m]
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]
      rw [← hc] at henv
      exact mul_le_mul_of_nonneg_right henv (integral_nonneg fun _ ↦ norm_nonneg _)
    have hlow : a * k ≤ lower := by
      have hs := pow_le_pow_left₀ (show 0 ≤ τ * (k : ℝ) by positivity) hcount 2
      have hh := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hs (by positivity : 0 ≤ 3 * (k : ℝ))) hl.le
      refine le_trans ?_ hh
      apply Eq.le
      dsimp only [a]
      field_simp [hk₀.ne']
    have hrbox : (k : ℝ) * r ^ 2 = Real.log k ^ 2 := by
      dsimp only [r, fourierBoxRadius]
      rw [div_pow, Real.sq_sqrt hk₀.le, mul_comm, div_mul_cancel₀ _ hk₀.ne']
    let f₁ := u + 2 * (n + 1 : ℝ) * Real.exp (-(lower / 2) * r ^ 2 / 2)
    have hf₁ : f₁ ≤ 2 * b := by
      have hh := mul_le_mul_of_nonneg_right hlow (sq_nonneg r)
      rw [mul_assoc a, hrbox] at hh
      have hAnn : -(lower / 2) * r ^ 2 / 2 ≤ -(a / 4) * Real.log k ^ 2 := by linarith only [hh]
      have hAnn' := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hAnn) (by positivity : (0 : ℝ) ≤ 2 * k)
      change u < b at houterRate
      change 2 * (k : ℝ) * Real.exp (-(a / 4) * Real.log k ^ 2) < b at hannRate
      dsimp only [f₁]
      rw [show (n + 1 : ℝ) = k by norm_num [k]]
      linarith only [hAnn', houterRate, hannRate]
    have hcoef : f₁ ≤ 1 / 2 := by
      have hb : b ≤ 1 / 4 := min_le_left _ _
      linarith only [hf₁, hb]
    have hε : ∀ x ∈ realPhaseBox (α := Fin k) r, ‖degreeFourierLocalError A q x‖ ≤ 1 :=
      hrem.2.2 A q
    have hcoef' : u + 2 * (n + 1 : ℝ) * Real.exp
        (-(l * ((m : ℝ) ^ 2 / (3 * (n + 1 : ℝ))) / 2) * r ^ 2 / 2) ≤ 1 / 2 := by
      simpa only [f₁, lower, k, Nat.cast_add, Nat.cast_one] using (show f₁ ≤ 1 / 2 from hcoef)
    have hFin := probability_residual_degreeAtom_and_fourier_tail_le_of_fourier_rates S hm q d hl hq hBig
      hrem.1 hrem.2.1 hε hul hcoef' ho'
    have hlower : 0 < lower := (mul_pos ha hk₀).trans_le hlow
    have hquad (x : Fin k → ℝ) : lower * ∑ i, x i ^ 2 ≤ x ⬝ᵥ (Q *ᵥ x) := by
      rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
      simpa only [lower, m, A, Q, Fintype.card_fin] using
        (degreeCovariance_outside_overlap_bounds S hm q l hl.le hq x).1
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
      rw [star_trivial]
      exact (mul_pos hlower (Finset.sum_pos' (fun _ _ ↦ sq_nonneg _)
        ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩)).trans_le (hquad v)
    have hd : Q.det ≤ ((k : ℝ) / 2) ^ k := by
      have h := degreeCovariance_outside_overlap_det_le S hm q
      rw [Fintype.card_fin] at h
      have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast Nat.succ_pos n
      exact h.trans (pow_le_pow_left₀ (by linarith only [hk₁]) (by linarith) k)
    have hNorm : Real.exp (-(k : ℝ) / 2 * Real.log k - Real.log Real.pi / 2 * k) ≤ Ξ := by
      change _ ≤ phaseGaussianScale Q
      rw [phaseGaussianScale_eq Q hQ]
      simpa only [Real.log_one, abs_zero, add_zero, Fintype.card_fin] using
        (exp_le_gaussian_atom_normalizer (n := k) (c := 1) (Nat.succ_pos n) hQ.det_pos zero_lt_one hd)
    have hBad' : bad ≤ c * Ξ := by
      let b₁ := -(k : ℝ) / 2 * Real.log k - Real.log Real.pi / 2 * k
      have hM : (k : ℝ) * Real.log k ^ 2 ≤ M := Nat.le_ceil _
      have h₁ := mul_le_mul_of_nonpos_left hM (neg_nonpos.mpr hcBad.le)
      let b₂ := -cBad * k * Real.log k ^ 2
      have h₂ : Real.exp (b₂ - b₁) ≤ c := by
        refine le_trans (le_of_eq (congrArg Real.exp ?_)) hbadRate.le
        dsimp only [b₁, b₂]
        ring
      calc
        bad ≤ Real.exp b₂ := Real.exp_le_exp.mpr (by dsimp only [b₂]; nlinarith only [h₁])
        _ = Real.exp (b₂ - b₁) * Real.exp b₁ := by rw [← Real.exp_add, sub_add_cancel]
        _ ≤ c * Ξ := mul_le_mul h₂ hNorm (Real.exp_nonneg _) hc₀.le
    have hΞ : 0 ≤ Ξ := (Real.exp_nonneg _).trans hNorm
    have hBad : bad ≤ Ξ :=
      hBad'.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) (ε / 2)) hΞ)
    let K := (1 / 96 : ℝ)
    let κ := 4 * (2 * r) ^ 3 * K * ((k : ℝ) - 1) * Real.sqrt k * Real.sqrt lower⁻¹
    let C := Real.exp (1 + 24 * K * ((k : ℝ) - 1) * k * lower⁻¹ ^ 2 + κ ^ 2 / 2)
    have hC : C ≤ cost := Real.exp_le_exp.mpr (hcost lower hlow)
    have hFin' : (graphLaw q).real (degreeAtom A d) ≤ 4 * C * Ξ + 2 * bad := by
      simpa only [C, Ξ, κ, lower, m, k, Nat.cast_add, Nat.cast_one] using hFin.1
    have hFinal : (graphLaw q).real (degreeAtom A d) ≤ (4 * cost + 2) * Ξ := by
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 4)) hΞ
      linarith only [hFin', hh, hBad]
    have hFinal' : (graphLaw q).real (degreeAtom A d) ≤
        (4 * cost + 2) / ((Real.sqrt (2 * Real.pi)) ^ k * Real.sqrt Q.det) := by
      change (graphLaw q).real (degreeAtom A d) ≤ (4 * cost + 2) * phaseGaussianScale Q at hFinal
      rwa [phaseGaussianScale_eq Q hQ, mul_one_div] at hFinal
    refine ⟨hFinal', ?_⟩
    have htail : (∫ t in (phaseBox (0 : PhaseCircle) r ∪ phaseBox (Real.pi : PhaseCircle) r)ᶜ,
        f t ∂phaseLaw) ≤ bad + 2 * f₁ * ((2 * C) * Ξ + bad) := by
      simpa only [f, f₁, C, Ξ, κ, lower, m, k, Nat.cast_add, Nat.cast_one] using hFin.2
    have hf₁₀ : 0 ≤ f₁ := add_nonneg hul (by positivity)
    have hscale : (2 * C) * Ξ + bad ≤ (2 * cost + 1) * Ξ := by
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 2)) hΞ
      linarith only [hh, hBad]
    have hcε : bad ≤ ε / 2 * Ξ := hBad'.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hΞ)
    have hbε : 2 * f₁ * (2 * cost + 1) ≤ ε / 2 := by
      have hh := hf₁.trans (mul_le_mul_of_nonneg_left (min_le_right (1 / 4) (ε / (8 * (2 * cost + 1))))
        (by norm_num : (0 : ℝ) ≤ 2))
      refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2))
        (by positivity : 0 ≤ 2 * cost + 1)).trans_eq ?_
      field_simp
      <;> ring
    have hterm : 2 * f₁ * ((2 * C) * Ξ + bad) ≤ ε / 2 * Ξ := by
      refine (mul_le_mul_of_nonneg_left hscale (by positivity)).trans ?_
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hbε hΞ
    exact htail.trans (by linarith only [hcε, hterm])

/-- Lemma B.1, stated in normalized Haar measure. The bound is uniform
over full arrays and all permitted overlap cliques. -/
theorem eventually_integral_degreeFourier_outside_small_boxes_le_uniform {l τ ε : ℝ}
    (hl : 0 < l) (hτ : 0 < τ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ (S : Finset (Fin k)) (q : Edge (Fin k) → Icc (0 : ℝ) 1)
      (d : Fin k → ℤ), τ * k ≤ (((Finset.univ : Finset (Fin k)) \ S).card : ℝ) →
      (∀ e, l ≤ (q e : ℝ) * (1 - q e)) →
      let A := edgesOutsideOverlap S
      let r := fourierBoxRadius k
      (∫ t in (phaseBox (0 : PhaseCircle) r ∪ phaseBox (Real.pi : PhaseCircle) r)ᶜ,
        ‖degreeFourier A q d t‖ ∂phaseLaw) ≤ ε * phaseGaussianScale (degreeCovariance A q) := by
  obtain ⟨C, _, h⟩ := eventually_probability_residual_degreeAtom_and_fourier_tail_le hl hτ
  filter_upwards [h ε hε] with k hk
  exact fun S q d hS hq ↦ (hk S q d hS hq).2

/-- The residual-atom bound with explicit normalization. -/
theorem eventually_probability_residual_degreeAtom_le {l τ : ℝ} (hl : 0 < l) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ (S : Finset (Fin k)) (q : Edge (Fin k) → Icc (0 : ℝ) 1) (d : Fin k → ℤ),
        τ * k ≤ (((Finset.univ : Finset (Fin k)) \ S).card : ℝ) →
        (∀ e, l ≤ (q e : ℝ) * (1 - q e)) →
        (graphLaw q).real (degreeAtom (edgesOutsideOverlap S) d) ≤
          C / ((Real.sqrt (2 * Real.pi)) ^ k *
            Real.sqrt (degreeCovariance (edgesOutsideOverlap S) q).det) := by
  obtain ⟨C, hC, h⟩ := eventually_probability_residual_degreeAtom_and_fourier_tail_le hl hτ
  refine ⟨C, hC, ?_⟩
  filter_upwards [h 1 zero_lt_one] with k hk
  exact fun S q d hS hq ↦ (hk S q d hS hq).1

/-- Proposition C.1 in terms of the probability interval in the manuscript. -/
theorem probability_residual_degreeAtom_le_uniform {δ ρ : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ < 1 / 2) (_hρ : 0 < ρ) (hρ₁ : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀,
      ∀ (S : Finset (Fin k)) (q : Edge (Fin k) → Icc (0 : ℝ) 1) (d : Fin k → ℤ),
        (S.card : ℝ) ≤ ρ * k →
        (∀ e, δ ≤ (q e : ℝ) ∧ (q e : ℝ) ≤ 1 - δ) →
        (graphLaw q).real (degreeAtom (edgesOutsideOverlap S) d) ≤
          C / ((Real.sqrt (2 * Real.pi)) ^ k *
            Real.sqrt (degreeCovariance (edgesOutsideOverlap S) q).det) := by
  obtain ⟨C, hC, h⟩ := eventually_probability_residual_degreeAtom_le
    (l := δ * (1 - δ)) (τ := 1 - ρ) (mul_pos hδ (by linarith)) (sub_pos.mpr hρ₁)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp h
  refine ⟨C, hC, k₀, fun k hk S q d hS hq ↦ hk₀ k hk S q d ?_ ?_⟩
  · have hm := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rw [Finset.card_univ, Fintype.card_fin] at hm
    have hm' : (((Finset.univ : Finset (Fin k)) \ S).card : ℝ) + S.card = k := by exact_mod_cast hm
    linarith only [hm', hS]
  · intro e
    nlinarith only [mul_nonneg (sub_nonneg.mpr (hq e).1) (sub_nonneg.mpr (hq e).2)]

end BoundedEdgeRegularSubgraphs
