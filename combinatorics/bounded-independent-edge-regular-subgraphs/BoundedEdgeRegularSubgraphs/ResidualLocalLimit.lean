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

/-- The uniform residual-atom upper bound with a positive variance floor
and a fixed positive fraction of undeleted vertices. -/
theorem eventually_probability_residual_degreeAtom_le {l τ : ℝ} (hl : 0 < l) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ (S : Finset (Fin k)) (q : Edge (Fin k) → Icc (0 : ℝ) 1) (d : Fin k → ℤ),
        τ * k ≤ (((Finset.univ : Finset (Fin k)) \ S).card : ℝ) →
        (∀ e, l ≤ (q e : ℝ) * (1 - q e)) →
        (graphLaw q).real (degreeAtom (edgesOutsideOverlap S) d) ≤
          C / ((Real.sqrt (2 * Real.pi)) ^ k *
            Real.sqrt (degreeCovariance (edgesOutsideOverlap S) q).det) := by
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
  have E₁ := eventually_valid_fourier_cutoffs hτ hη
  have E₂ := (tendsto_fourierOuterEnvelope hη hγ hτ).eventually_lt_const
    (show (0 : ℝ) < 1 / 4 by norm_num)
  have E₃ : ∀ᶠ k : ℕ in atTop, 2 * k * Real.exp (-(a / 4) * Real.log k ^ 2) < 1 / 4 := by
    have h := (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_nat_mul_exp_neg_log_sq (show 0 < a / 4 by positivity))
    simp only [mul_zero] at h
    filter_upwards [h.eventually_lt_const (show (0 : ℝ) < 1 / 4 by norm_num)] with k hk
    simpa only [mul_assoc] using hk
  have E₄ := eventually_uniform_fourierBox_cost ha
  have E₅ := eventually_degreeFourierLocalError_le_one
  have E₆ := (tendsto_exp_many_bad_normalized (C := Real.log Real.pi / 2) hcBad).eventually_lt_const zero_lt_one
  refine ⟨4 * cost + 2, by dsimp only [cost]; positivity, ?_⟩
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
    have hcoef : u + 2 * (n + 1 : ℝ) * Real.exp (-(lower / 2) * r ^ 2 / 2) ≤ 1 / 2 := by
      have hh := mul_le_mul_of_nonneg_right hlow (sq_nonneg r)
      rw [mul_assoc a, hrbox] at hh
      have hAnn : -(lower / 2) * r ^ 2 / 2 ≤ -(a / 4) * Real.log k ^ 2 := by linarith only [hh]
      have hAnn' := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hAnn) (by positivity : (0 : ℝ) ≤ 2 * k)
      change u < 1 / 4 at houterRate
      change 2 * (k : ℝ) * Real.exp (-(a / 4) * Real.log k ^ 2) < 1 / 4 at hannRate
      rw [show (n + 1 : ℝ) = k by norm_num [k]]
      linarith only [hAnn', houterRate, hannRate]
    have hε : ∀ x ∈ realPhaseBox (α := Fin k) r, ‖degreeFourierLocalError A q x‖ ≤ 1 :=
      hrem.2.2 A q
    have hcoef' : u + 2 * (n + 1 : ℝ) * Real.exp
        (-(l * ((m : ℝ) ^ 2 / (3 * (n + 1 : ℝ))) / 2) * r ^ 2 / 2) ≤ 1 / 2 := by
      simpa only [lower, k, Nat.cast_add, Nat.cast_one] using hcoef
    have hFin := probability_residual_degreeAtom_le_of_fourier_rates S hm q d hl hq hBig
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
    have hBad : bad ≤ Ξ := by
      have hM : (k : ℝ) * Real.log k ^ 2 ≤ M := Nat.le_ceil _
      have h₁ := mul_le_mul_of_nonpos_left hM (neg_nonpos.mpr hcBad.le)
      have h₂ := Real.exp_lt_one_iff.mp hbadRate
      change -cBad * k * Real.log k ^ 2 + k * Real.log k / 2 + Real.log Real.pi / 2 * k < 0 at h₂
      refine (Real.exp_le_exp.mpr ?_).trans hNorm
      linarith only [h₁, h₂]
    let K := (1 / 96 : ℝ)
    let κ := 4 * (2 * r) ^ 3 * K * ((k : ℝ) - 1) * Real.sqrt k * Real.sqrt lower⁻¹
    let C := Real.exp (1 + 24 * K * ((k : ℝ) - 1) * k * lower⁻¹ ^ 2 + κ ^ 2 / 2)
    have hC : C ≤ cost := Real.exp_le_exp.mpr (hcost lower hlow)
    have hΞ : 0 ≤ Ξ := (Real.exp_nonneg _).trans hNorm
    have hFin' : (graphLaw q).real (degreeAtom A d) ≤ 4 * C * Ξ + 2 * bad := by
      simpa only [C, Ξ, κ, lower, m, k, Nat.cast_add, Nat.cast_one] using hFin
    have hFinal : (graphLaw q).real (degreeAtom A d) ≤ (4 * cost + 2) * Ξ := by
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 4)) hΞ
      linarith only [hFin', hh, hBad]
    change (graphLaw q).real (degreeAtom A d) ≤ (4 * cost + 2) * phaseGaussianScale Q at hFinal
    rwa [phaseGaussianScale_eq Q hQ, mul_one_div] at hFinal

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
