module

public import BoundedEdgeRegularSubgraphs.BalancedInducedRegularity
public import BoundedEdgeRegularSubgraphs.OrderEventTransport
public import BoundedEdgeRegularSubgraphs.StructuralLargeCells
import Mathlib.Tactic

/-!
# Transferring the near-balance success bound to finite blocks
-/

public section

open Filter MeasureTheory Set Function

namespace BoundedEdgeRegularSubgraphs

/-- The exact-order success bound of Theorem 4.1 on any finite ordered domain. -/
theorem eventually_exactOrder_success_of_nearBalance {ξ M : ℝ}
    (hξ : 0 < ξ) (hξ₁ : ξ < 1 / 2) (hM : 0 ≤ M) :
    ∃ L p₀ : ℝ, 1 ≤ L ∧ 0 < p₀ ∧ p₀ ≤ 1 ∧ ∀ᶠ k : ℕ in atTop,
      ∀ {β : Type} [Fintype β] [LinearOrder β],
        L * (k : ℝ) * Real.sqrt k ≤ (Fintype.card β : ℝ) →
        ∀ q : Edge β → Icc (0 : ℝ) 1,
          (∀ e, ξ ≤ (q e : ℝ) ∧ (q e : ℝ) ≤ 1 - ξ) →
          (∃ p ∈ Icc ξ (1 - ξ), ∀ i,
            |degreeSum (fun e ↦ (q e : ℝ)) i / ((Fintype.card β : ℝ) - 1) - p| ≤
              Real.sqrt (M / k)) →
          p₀ ≤ (graphLaw q).real (exactOrderEvent k) := by
  obtain ⟨L, p₀, hL, hp₀, hp₁, h⟩ := eventually_fixedDegree_success_of_nearBalance hξ hξ₁ hM
  refine ⟨L, p₀, hL, hp₀, hp₁, ?_⟩
  filter_upwards [h, eventually_ge_atTop (2 : ℕ)] with k hk hk₂
  intro β _ _ hSize q hq hRow
  obtain ⟨p, hp, hRow⟩ := hRow
  let N := Fintype.card β
  let f : Fin N ≃o β := Fintype.orderIsoFinOfCardEq β rfl
  let q' := q ∘ edgeEquiv f
  have hN : 1 ≤ N := by
    have hk₀ : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hS : (1 : ℝ) ≤ Real.sqrt k := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hk₀
    have h := mul_le_mul hL hk₀ (by norm_num : (0 : ℝ) ≤ 1) (by linarith only [hL])
    have hh := mul_le_mul h hS (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ L * (k : ℝ))
    have hN' : (1 : ℝ) ≤ N := by simpa only [one_mul] using hh.trans hSize
    exact_mod_cast hN'
  obtain ⟨d, F, _, _, _, _, hF, hProb⟩ := hk N hSize q' p (fun e ↦ hq (edgeEquiv f e)) hp (by
    intro i
    rw [sampleRowMean_univ_eq_degree _ (by simpa only [Fintype.card_fin] using hN), Fintype.card_fin]
    have he := degreeSum_reindex f (fun e ↦ (q e : ℝ)) i
    change degreeSum (fun e ↦ (q' e : ℝ)) i = _ at he
    rw [he]
    exact hRow (f i))
  have hFail := probability_exactOrder_failure_le_no_candidate q' d F hF
  have hCompl : (⋂ S ∈ F, (inducedDegreeAtom S d)ᶜ) =
      (⋃ S ∈ F, inducedDegreeAtom S d)ᶜ := by
    simp only [compl_iUnion]
  have : IsProbabilityMeasure (graphLaw q') := by unfold graphLaw; infer_instance
  have : IsProbabilityMeasure (graphLaw q) := by unfold graphLaw; infer_instance
  rw [probability_exactOrder_failure_reindex f q, hCompl,
    probReal_compl_eq_one_sub (measurableSet_exactOrderEvent k),
    probReal_compl_eq_one_sub (F.measurableSet_biUnion (fun S _ ↦ measurableSet_inducedDegreeAtom S d))] at hFail
  linarith only [hFail, hProb]

theorem mul_sqrt_eq_rpow_three_halves (x : ℝ) (hx : 0 ≤ x) :
    x * Real.sqrt x = x ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, show x * x ^ (1 / 2 : ℝ) = x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) by rw [Real.rpow_one],
    ← Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num)]
  norm_num

theorem sqrt_div_sq_eq_mul_inv_sqrt (M : ℝ) (hM : 0 ≤ M) (k : ℕ) :
    Real.sqrt (M ^ 2 / (k : ℝ)) = M * (Real.sqrt k)⁻¹ := by
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hM, div_eq_mul_inv]

/-- Theorem 6.1, with the finite large-cell assumption (6.1). -/
theorem eventually_exactOrder_failure_le_of_largeBalancedCells {ξ s c₀ C₀ : ℝ}
    (hξ : 0 < ξ) (hξ₁ : ξ < 1 / 2) (hs : 0 ≤ s) (hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      (k : ℝ) ≤ a * (n : ℝ) ^ (2 / (s + 3)) →
        ∀ q : Edge (Fin n) → Icc (0 : ℝ) 1, HasFloor ξ q → HasLargeBalancedCells s c₀ C₀ q →
          (graphLaw q).real (exactOrderEvent k)ᶜ ≤ Real.exp (-c * (n : ℝ) / (k : ℝ) ^ (3 / 2 : ℝ)) := by
  obtain ⟨H, p₀, hH, hp₀, hp₁, hS⟩ :=
    eventually_exactOrder_success_of_nearBalance hξ hξ₁ (sq_nonneg (C₀ + 1))
  have hS' : ∀ᶠ k : ℕ in atTop, ∀ {β : Type} [Fintype β] [LinearOrder β],
      Fintype.card β = regularBlockSize H k →
      ∀ q : Edge β → Icc (0 : ℝ) 1, (∀ e, ξ ≤ (q e : ℝ) ∧ (q e : ℝ) ≤ 1 - ξ) →
        (∃ p ∈ Icc ξ (1 - ξ), ∀ i, |degreeSum (fun e ↦ (q e : ℝ)) i /
          ((Fintype.card β : ℝ) - 1) - p| ≤ (C₀ + 1) * (Real.sqrt k)⁻¹) →
        p₀ ≤ (graphLaw q).real (exactOrderEvent k) := by
    filter_upwards [hS] with k hk
    intro β _ _ hβ q hq hRow
    have hSize : H * (k : ℝ) * Real.sqrt k ≤ (Fintype.card β : ℝ) := by
      rw [hβ]
      exact Nat.le_ceil (H * (k : ℝ) * Real.sqrt k)
    apply hk hSize q hq
    rwa [sqrt_div_sq_eq_mul_inv_sqrt (C₀ + 1) (by positivity)]
  obtain ⟨a, c, ha, hc, hBound⟩ :=
    exactOrder_failure_le_of_largeBalancedCells_and_block_success hs hc₀ hH hp₀ hp₁ hS'
  refine ⟨a, c, ha, hc, ?_⟩
  filter_upwards [hBound] with k hk
  intro n hn q hq hCell
  simpa only [mul_sqrt_eq_rpow_three_halves (k : ℝ) (Nat.cast_nonneg k)] using hk n hn q hq hCell

/-- Corollary 6.2 in the uniform form of Theorem 1.1(3). -/
theorem theorem1_1_lipschitz : Theorem1_1_lipschitz := by
  intro ξ L d hξ hξ₁ hL hd
  obtain ⟨a, c, ha, hc, hCell⟩ :=
    eventually_exactOrder_failure_le_of_largeBalancedCells hξ hξ₁ (Nat.cast_nonneg d)
      (show (0 : ℝ) < ((2 : ℝ) ^ d)⁻¹ by positivity) (show 0 ≤ 2 * L by positivity)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hCell.and (eventually_ge_atTop (1 : ℕ)))
  refine ⟨a, c, ha, hc, k₀, 1, (hk₀ k₀ le_rfl).2, ?_⟩
  intro n _ k hk hSize W hSymm hLip hFloor x
  exact (hk₀ k hk).1 n hSize _ (fun e ↦ hFloor _ _) (hasLargeBalancedCells_of_lipschitz x W hSymm hLip)

/-- Corollary 6.4 in the uniform form of Theorem 1.1(4). -/
theorem theorem1_1_lowRank : Theorem1_1_lowRank := by
  intro ξ r hξ hξ₁ hr
  have hExp : 2 / (((r : ℝ) + 1) / 2 + 3) = 4 / ((r : ℝ) + 7) := by
    field_simp <;> ring
  obtain ⟨a, c, ha, hc, hCell⟩ :=
    eventually_exactOrder_failure_le_of_largeBalancedCells hξ hξ₁
      (show 0 ≤ ((r : ℝ) + 1) / 2 by positivity)
      (show 0 < ((3 ^ r * (2 * (r : ℝ) ^ 2 + 1))⁻¹) by positivity)
      (show 0 ≤ 1 + (r : ℝ) ^ 2 by positivity)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hCell.and (eventually_ge_atTop (1 : ℕ)))
  refine ⟨a, c, ha, hc, k₀, 1, (hk₀ k₀ le_rfl).2, ?_⟩
  intro n _ k hk hSize q hq hRank
  exact (hk₀ k hk).1 n (by rwa [hExp]) q hq (hasLargeBalancedCells_of_rank q hRank)

end BoundedEdgeRegularSubgraphs
