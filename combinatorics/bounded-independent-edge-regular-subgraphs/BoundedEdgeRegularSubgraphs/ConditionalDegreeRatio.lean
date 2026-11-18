module

public import BoundedEdgeRegularSubgraphs.CenteredDegreeAtom
public import BoundedEdgeRegularSubgraphs.OverlapProbabilityRatio
import Mathlib.Tactic

/-!
# Corollary C.2: the uniform conditional degree ratio
-/

public section

open Filter MeasureTheory Matrix Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- Exposing the edges of any permitted overlap changes a centred
degree atom by at most the uniform ratio from Corollary C.2. -/
theorem probability_conditional_degreeAtom_ratio_uniform {δ ρ : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ < 1 / 2) (hρ : 0 < ρ) (hρ₁ : ρ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ (S : Finset (Fin k)) (q : Edge (Fin k) → Icc (0 : ℝ) 1)
        (h : Edge (Fin k) → ℝ) (d : Fin k → ℤ),
        (S.card : ℝ) ≤ ρ * k →
        (∀ e, δ ≤ (q e : ℝ) ∧ (q e : ℝ) ≤ 1 - δ) →
        (∀ e ∈ edgesInside S, h e = 0 ∨ h e = 1) →
        (∀ i, (d i : ℝ) = degreeSum (fun e ↦ (q e : ℝ)) i) → Even (∑ i, d i) →
        (((graphLaw q).real (degreeAtom Finset.univ d ∩ overlapAssignmentEvent S h) /
          (graphLaw q).real (overlapAssignmentEvent S h)) /
          (graphLaw q).real (degreeAtom Finset.univ d)) ≤ K * Real.exp (K * (S.card : ℝ) ^ 2 / k) := by
  let l := δ * (1 - δ)
  let τ := 1 - ρ
  let a := l * τ ^ 2 / 3
  have hl : 0 < l := mul_pos hδ (by linarith)
  have hτ : 0 < τ := sub_pos.mpr hρ₁
  have ha : 0 < a := by dsimp only [a]; positivity
  obtain ⟨c, C, hc, _, hFull⟩ := centered_degreeAtom_uniform_asymptotic_of_variance_floor hl
  obtain ⟨B, hB, k₀, hRes⟩ := probability_residual_degreeAtom_le_uniform hδ hδ₁ hρ hρ₁
  let K := max (B / c) (1 / (8 * a))
  have hK : 0 < K := (div_pos hB hc).trans_le (le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  have hmEvent : ∀ᶠ k : ℕ in atTop, (3 : ℝ) ≤ τ * (k : ℝ) := by
    have hnat : Tendsto (fun k : ℕ ↦ (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [hnat.eventually_ge_atTop (3 / τ)] with k hk
    simpa only [mul_comm] using (div_le_iff₀ hτ).mp hk
  filter_upwards [hFull 1 zero_lt_one, eventually_ge_atTop k₀, hmEvent,
    eventually_ge_atTop (1 : ℕ)] with k hFull' hk₀ hmEvent' hk₁
  intro S q h d hS hq hh hd hEven
  let m := ((Finset.univ : Finset (Fin k)) \ S).card
  let N := (Real.sqrt (2 * Real.pi)) ^ k
  let low := l * ((m : ℝ) ^ 2 / (3 * (k : ℝ)))
  have hk : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hm' : (m : ℝ) + S.card = k := by
    have hv := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rw [Finset.card_univ, Fintype.card_fin] at hv
    exact_mod_cast hv
  have hcount : τ * (k : ℝ) ≤ m := by dsimp only [τ]; linarith only [hm', hS]
  have hm : 3 ≤ m := by exact_mod_cast hmEvent'.trans hcount
  have hvar (e : Edge (Fin k)) : l ≤ (q e : ℝ) * (1 - q e) := by
    dsimp only [l]
    nlinarith only [mul_nonneg (sub_nonneg.mpr (hq e).1) (sub_nonneg.mpr (hq e).2)]
  have hFull'' := (hFull' q d hvar hd hEven).2.1
  have hRes' := hRes k hk₀ S q (d - degreeVector (edgesInside S) h) hS hq
  have hN : 0 < N := by dsimp only [N]; positivity
  simp only [← div_div] at hFull'' hRes'
  have hpos := probability_overlapAssignment_pos q S h
    (fun e _ ↦ ⟨hδ.trans_le (hq e).1, (hq e).2.trans_lt (by linarith only [hδ])⟩) hh
  have hr := probability_conditional_ratio_le_of_atom_bounds S hm q l hl hvar h d
    (div_pos hc hN) (div_nonneg hB.le hN.le) hpos hFull'' hRes'
  simp only [Fintype.card_fin] at hr
  refine hr.trans ?_
  change (B / N) / (c / N) *
    Real.exp ((S.card : ℝ) * ((S.card : ℝ) - 1) / (8 * low)) ≤ _
  have hLower : a * (k : ℝ) ≤ low := by
    have hp := pow_le_pow_left₀ (show 0 ≤ τ * (k : ℝ) by positivity) hcount 2
    refine le_trans ?_ (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hp (show 0 ≤ 3 * (k : ℝ) by positivity)) hl.le)
    apply Eq.le
    dsimp only [a]
    field_simp [hk.ne']
  have hLow : 0 < low := (mul_pos ha hk).trans_le hLower
  have hpow : (S.card : ℝ) * ((S.card : ℝ) - 1) ≤ (S.card : ℝ) ^ 2 := by
    nlinarith only [Nat.cast_nonneg (α := ℝ) S.card]
  have hExp : (S.card : ℝ) * ((S.card : ℝ) - 1) / (8 * low) ≤ K * (S.card : ℝ) ^ 2 / k := by
    calc
      _ ≤ (S.card : ℝ) ^ 2 / (8 * low) :=
        div_le_div_of_nonneg_right hpow (by positivity)
      _ ≤ (S.card : ℝ) ^ 2 / (8 * (a * (k : ℝ))) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          (mul_le_mul_of_nonneg_left hLower (by norm_num))
      _ = (1 / (8 * a)) * (S.card : ℝ) ^ 2 / k := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)) hk.le
  rw [show (B / N) / (c / N) = B / c by field_simp]
  exact mul_le_mul (le_max_left _ _) (Real.exp_le_exp.mpr hExp) (Real.exp_nonneg _) hK.le

end BoundedEdgeRegularSubgraphs
