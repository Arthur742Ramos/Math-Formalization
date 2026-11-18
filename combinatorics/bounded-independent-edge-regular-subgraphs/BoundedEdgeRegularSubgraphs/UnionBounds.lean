module

public import BoundedEdgeRegularSubgraphs.MeanDrift
import BoundedEdgeRegularSubgraphs.Induce
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

public section

open MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- Proposition 9.1 for a specified induced vertex set in an ambient array. -/
theorem probability_induced_regular_le (p : Edge α → Set.Icc (0 : ℝ) 1)
    (S : Finset α) (hk : 3 ≤ S.card) :
    (graphLaw p).real (inducedRegularEvent S) ≤
      Real.exp (-2 * degreeVariation (induce S p) / (S.card - 2 : ℝ)) := by
  rw [probability_induced_regular_eq]
  simpa only [Fintype.card_coe] using probability_regular_le (induce S p)
    (by rwa [Fintype.card_coe])

/-- The finite union bound at a prescribed order, with one summand per vertex set. -/
theorem probability_exact_order_le (p : Edge α → Set.Icc (0 : ℝ) 1)
    (k : ℕ) (hk : 3 ≤ k) :
    (graphLaw p).real (exactOrderEvent k) ≤
      ∑ S : {S : Finset α // S.card = k},
        Real.exp (-2 * degreeVariation (induce S.val p) / (k - 2 : ℝ)) := by
  classical
  refine (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum fun S _ ↦ ?_)
  have hkS : 3 ≤ S.val.card := by
    rwa [S.property]
  simpa only [S.property] using probability_induced_regular_le p S.val hkS

/-- The union bound across all orders at least k. -/
theorem probability_at_least_order_le (p : Edge α → Set.Icc (0 : ℝ) 1)
    (k : ℕ) (hk : 3 ≤ k) :
    (graphLaw p).real (atLeastOrderEvent k) ≤
      ∑ S : {S : Finset α // k ≤ S.card},
        Real.exp (-2 * degreeVariation (induce S.val p) / (S.val.card - 2 : ℝ)) := by
  classical
  refine (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum fun S _ ↦ ?_)
  exact probability_induced_regular_le p S.val (hk.trans S.property)

omit [LinearOrder α] in
theorem card_fixed_order (k : ℕ) :
    Fintype.card {S : Finset α // S.card = k} = (Fintype.card α).choose k := by
  classical
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter (fun S : Finset α ↦ S.card = k)) =
      (Finset.univ : Finset α).powersetCard k := by
    ext S
    simp
  rw [h, Finset.card_powersetCard, Finset.card_univ]

/-- Positive probability of a regular k-set forces a k-set with sufficiently small variation. -/
theorem exists_small_variation_of_probability_exact_order_ge
    (p : Edge α → Set.Icc (0 : ℝ) 1) (k : ℕ) (hk : 3 ≤ k) {γ : ℝ}
    (hγ : 0 < γ) (hprob : γ ≤ (graphLaw p).real (exactOrderEvent k)) :
    ∃ S : Finset α, S.card = k ∧
      degreeVariation (induce S p) ≤ ((k : ℝ) - 2) / 2 *
        Real.log (((Fintype.card α).choose k : ℝ) / γ) := by
  classical
  let T := {S : Finset α // S.card = k}
  let N : ℝ := Fintype.card T
  let b : T → ℝ := fun S ↦
    Real.exp (-2 * degreeVariation (induce S.val p) / (k - 2 : ℝ))
  have hsum : γ ≤ ∑ S, b S := hprob.trans (probability_exact_order_le p k hk)
  have hT : Nonempty T := by
    by_contra hn
    have : IsEmpty T := not_nonempty_iff.mp hn
    have hγ₀ : γ ≤ 0 := by simpa using hsum
    exact hγ.not_ge hγ₀
  have hN : 0 < N := by
    change 0 < (Fintype.card T : ℝ)
    exact_mod_cast Fintype.card_pos_iff.mpr hT
  have havg : ∃ S : T, γ / N ≤ b S := by
    by_contra! h
    have hlt := Finset.sum_lt_sum_of_nonempty
      (Finset.univ_nonempty (α := T)) (fun S _ ↦ h S)
    have hconst : (∑ _ : T, γ / N) = γ := by
      simp [Finset.sum_const, nsmul_eq_mul, ← show (Fintype.card T : ℝ) = N from rfl,
        mul_div_cancel₀]
    rw [hconst] at hlt
    exact hlt.not_ge hsum
  obtain ⟨S, hS⟩ := havg
  have hlog : Real.log (γ / N) ≤ -2 * degreeVariation (induce S.val p) / (k - 2 : ℝ) := by
    apply Real.exp_le_exp.mp
    rw [Real.exp_log (div_pos hγ hN)]
    exact hS
  have hneg : Real.log (γ / N) = - Real.log (N / γ) := by
    rw [Real.log_div hγ.ne' hN.ne', Real.log_div hN.ne' hγ.ne']
    ring
  have hk' : 0 < (k - 2 : ℝ) := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [hneg, le_div_iff₀ hk'] at hlog
  have hNchoose : N = ((Fintype.card α).choose k : ℝ) := by
    change (Fintype.card T : ℝ) = ((Fintype.card α).choose k : ℝ)
    exact_mod_cast card_fixed_order (α := α) k
  refine ⟨S.val, S.property, ?_⟩
  rw [← hNchoose]
  linarith only [hlog]

/-- A uniform lower bound on variation gives the fixed-order power bound in §9. -/
theorem probability_exact_order_le_of_large_variation
    (p : Edge α → Set.Icc (0 : ℝ) 1) (k : ℕ) (hk : 3 ≤ k)
    (hkn : k ≤ Fintype.card α) (δ : ℝ)
    (hV : ∀ S : Finset α, S.card = k →
      (1 + δ) * (k - 2 : ℝ) *
        Real.log ((Fintype.card α).choose k : ℝ) / 2 ≤ degreeVariation (induce S p)) :
    (graphLaw p).real (exactOrderEvent k) ≤ ((Fintype.card α).choose k : ℝ) ^ (-δ) := by
  classical
  let C := ((Fintype.card α).choose k : ℝ)
  have hC : 0 < C := by
    change 0 < ((Fintype.card α).choose k : ℝ)
    exact_mod_cast Nat.choose_pos hkn
  have hk' : 0 < (k - 2 : ℝ) := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  refine (probability_exact_order_le p k hk).trans ?_
  calc
    _ ≤ ∑ _ : {S : Finset α // S.card = k}, Real.exp (-(1 + δ) * Real.log C) := by
      refine Finset.sum_le_sum (fun S _ ↦ Real.exp_le_exp.mpr ?_)
      apply (div_le_iff₀ hk').mpr
      have h := hV S.val S.property
      change (1 + δ) * (k - 2 : ℝ) * Real.log C / 2 ≤ _ at h
      linarith only [h]
    _ = C * Real.exp (-(1 + δ) * Real.log C) := by
      simp [Finset.sum_const, nsmul_eq_mul, C]
    _ = _ := by
      change C * Real.exp (-(1 + δ) * Real.log C) = C ^ (-δ)
      rw [Real.rpow_def_of_pos hC]
      calc
        _ = Real.exp (Real.log C) * Real.exp (-(1 + δ) * Real.log C) := by
          rw [Real.exp_log hC]
        _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Positive probability of a large regular set forces small variation at one of the possible orders. -/
theorem exists_small_variation_of_probability_at_least_order_ge
    (p : Edge α → Set.Icc (0 : ℝ) 1) (k : ℕ) (hk : 3 ≤ k) {γ : ℝ}
    (hγ : 0 < γ) (hprob : γ ≤ (graphLaw p).real (atLeastOrderEvent k)) :
    ∃ S : Finset α, k ≤ S.card ∧
      degreeVariation (induce S p) ≤ (S.card - 2 : ℝ) / 2 *
        Real.log (((Fintype.card α - k + 1 : ℕ) : ℝ) *
          ((Fintype.card α).choose S.card : ℝ) / γ) := by
  classical
  let orders := Finset.Icc k (Fintype.card α)
  have hevent : (atLeastOrderEvent k : Set (Edge α → ℝ)) =
      ⋃ j ∈ orders, exactOrderEvent j := by
    ext w
    simp only [atLeastOrderEvent, exactOrderEvent, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨S, hS⟩, hw⟩
      have hcard : S.card ≤ Fintype.card α := Finset.card_le_univ S
      exact ⟨S.card, Finset.mem_Icc.mpr ⟨hS, hcard⟩, ⟨⟨S, rfl⟩, hw⟩⟩
    · rintro ⟨j, hj, ⟨S, hS⟩, hw⟩
      have hkS : k ≤ S.card := by
        rw [hS]
        exact (Finset.mem_Icc.mp hj).1
      exact ⟨⟨S, hkS⟩, hw⟩
  have hsum : γ ≤ ∑ j ∈ orders, (graphLaw p).real (exactOrderEvent j) := by
    apply hprob.trans
    rw [hevent]
    exact measureReal_biUnion_finset_le orders exactOrderEvent
  have horders : orders.Nonempty := by
    by_contra h
    have hzero : orders = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hz : γ ≤ 0 := by simpa [hzero] using hsum
    exact hγ.not_ge hz
  have hcard : 0 < (orders.card : ℝ) := by exact_mod_cast horders.card_pos
  have havg : ∃ j ∈ orders, γ / (orders.card : ℝ) ≤ (graphLaw p).real (exactOrderEvent j) := by
    by_contra! h
    have hlt := Finset.sum_lt_sum_of_nonempty horders h
    have hconst : (∑ _ ∈ orders, γ / (orders.card : ℝ)) = γ := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀, hcard.ne']
    rw [hconst] at hlt
    exact hlt.not_ge hsum
  obtain ⟨j, hj, hprobj⟩ := havg
  have hj' : k ≤ j ∧ j ≤ Fintype.card α := Finset.mem_Icc.mp hj
  obtain ⟨S, hS, hvar⟩ := exists_small_variation_of_probability_exact_order_ge
    p j (hk.trans hj'.1) (div_pos hγ hcard) hprobj
  have hcount : orders.card = Fintype.card α - k + 1 := by
    dsimp [orders]
    rw [Nat.card_Icc]
    omega
  have hkS : k ≤ S.card := by
    rw [hS]
    exact hj'.1
  refine ⟨S, hkS, ?_⟩
  rw [hS]
  have hratio :
      ((Fintype.card α).choose j : ℝ) / (γ / (orders.card : ℝ)) =
        ((Fintype.card α - k + 1 : ℕ) : ℝ) * ((Fintype.card α).choose j : ℝ) / γ := by
    rw [div_div_eq_mul_div, hcount, mul_comm]
  rwa [hratio] at hvar

end BoundedEdgeRegularSubgraphs
