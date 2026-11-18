module

public import BoundedEdgeRegularSubgraphs.OverlapMass
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# The three overlap ranges at the balanced scale
-/

public section

open Filter Asymptotics
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

private theorem sum_geometric_range_le {x : ℝ} (hx : 0 ≤ x) (h₁ : x < 1) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), x ^ j) ≤ (1 - x)⁻¹ := by
  have hsum := summable_geometric_of_lt_one hx h₁
  rw [← tsum_geometric_of_lt_one hx h₁]
  exact Summable.sum_le_tsum _ (fun j _ ↦ pow_nonneg hx j) hsum

/-- The moment contributions of the small, intermediate and large
overlap regimes have a common bounded sum when the ambient size is
at least a constant times k to the power three halves. -/
theorem eventually_balanced_overlap_weight_sum_le {A E D : ℝ} (hA : 0 < A) (hE : 0 < E) (hD : 0 ≤ D) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ (μ : ℝ), 0 ≤ μ → μ ≤ Real.sqrt k → ∀ P : ℕ → ℝ,
        (∀ j, 0 ≤ P j) → (∑ j ∈ Finset.range (k + 1), P j) = 1 →
        (∀ j, 0 < j → j ≤ k → P j ≤ (Real.exp 1 * μ / j) ^ j) →
        let t := (k : ℝ) / (A * Real.log k)
        t ≤ (3 / 4 : ℝ) * k ∧
        (∑ j ∈ Finset.range (k + 1),
          if (j : ℝ) ≤ t then P j * Real.exp (E * (j : ℝ) ^ 2 / k)
          else if (j : ℝ) ≤ (3 / 4 : ℝ) * k then P j * Real.exp (D * (j : ℝ))
          else Real.exp (-(k : ℝ))) ≤ K := by
  let Q : ℝ := Real.exp (E * Real.exp 2 ^ 2)
  refine ⟨Q + 6, by dsimp only [Q]; linarith only [Real.exp_pos (E * Real.exp 2 ^ 2)], ?_⟩
  have hcast : Tendsto (fun k : ℕ ↦ (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun k : ℕ ↦ Real.log k) atTop atTop := Real.tendsto_log_atTop.comp hcast
  have hMid : ∀ᶠ k : ℕ in atTop, 2 * Real.exp (1 + D) * A * Real.log k ≤ Real.sqrt k := by
    have h := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto hcast).bound
      (show 0 < (1 / (2 * Real.exp (1 + D) * A) : ℝ) by positivity)
    filter_upwards [h, hlog.eventually_ge_atTop 1] with k hk hLog
    change ‖Real.log k‖ ≤ _ * ‖(k : ℝ) ^ (1 / 2 : ℝ)‖ at hk
    rw [Real.norm_of_nonneg (show 0 ≤ Real.log k by linarith only [hLog]),
      ← Real.sqrt_eq_rpow, Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hk
    have hk' : Real.log k ≤ Real.sqrt k / (2 * Real.exp (1 + D) * A) := by
      simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm (Real.sqrt _)] using hk
    simpa only [mul_comm (Real.log _)] using (le_div_iff₀ (by positivity)).1 hk'
  filter_upwards [hMid, hlog.eventually_ge_atTop (2 * E / A),
    hlog.eventually_ge_atTop (4 / (3 * A)), hlog.eventually_ge_atTop 1,
    eventually_ge_atTop (1 : ℕ)] with k hMid' hLogE hLogA hLog hk
  intro μ hμ₀ hμ P hP₀ hPSum hPow
  intro t
  have hk₀ : (0 : ℝ) < k := zero_lt_one.trans_le (by exact_mod_cast hk)
  have hL₀ : 0 < Real.log k := zero_lt_one.trans_le hLog
  have ht₀ : 0 < t := by dsimp only [t]; positivity
  have htρ : t ≤ (3 / 4 : ℝ) * k := by
    apply (div_le_iff₀ (mul_pos hA hL₀)).2
    have h := (div_le_iff₀ (by positivity : 0 < 3 * A)).1 hLogA
    have hh := mul_le_mul_of_nonneg_right h hk₀.le
    nlinarith only [hh]
  refine ⟨htρ, ?_⟩
  have hroot := Real.sq_sqrt hk₀.le
  have hHalf : Real.exp (-(1 / 2 : ℝ)) ≤ 2 / 3 := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    have h := Real.add_one_le_exp (1 / 2 : ℝ)
    linarith only [h]
  have hPoint (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
      (if (j : ℝ) ≤ t then P j * Real.exp (E * (j : ℝ) ^ 2 / k)
        else if (j : ℝ) ≤ (3 / 4 : ℝ) * k then P j * Real.exp (D * (j : ℝ))
        else Real.exp (-(k : ℝ))) ≤
      Q * P j + (2 / 3 : ℝ) ^ j + (1 / 2 : ℝ) ^ j + Real.exp (-(k : ℝ)) := by
    have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
    have hj' : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hQ : 0 ≤ Q * P j := mul_nonneg (Real.exp_nonneg _) (hP₀ j)
    have hG₁ : 0 ≤ (2 / 3 : ℝ) ^ j := by positivity
    have hG₂ : 0 ≤ (1 / 2 : ℝ) ^ j := by positivity
    have hG₃ := Real.exp_nonneg (-(k : ℝ))
    by_cases hs : (j : ℝ) ≤ t
    · rw [ite_eq_left hs]
      by_cases hsmall : (j : ℝ) ≤ Real.exp 2 * Real.sqrt k
      · have hA' : E * (j : ℝ) ^ 2 / k ≤ E * Real.exp 2 ^ 2 := by
          apply (div_le_iff₀ hk₀).2
          have hJ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hj' hsmall 2) hE.le
          rwa [mul_pow, hroot, ← mul_assoc] at hJ
        refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hA') (hP₀ j)).trans ?_
        change P j * Q ≤ _
        rw [mul_comm (P j) Q]
        linarith only [hG₁, hG₂, hG₃]
      · have hj₀ : (0 : ℝ) < j := (by positivity : 0 < Real.exp 2 * Real.sqrt k).trans (lt_of_not_ge hsmall)
        have hju : 0 < j := by exact_mod_cast hj₀
        have hBase : Real.exp 1 * μ / (j : ℝ) ≤ Real.exp (-1) := by
          apply (div_le_iff₀ hj₀).2
          have h := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hμ (Real.exp_nonneg 2)).trans
            (le_of_not_ge hsmall)) (Real.exp_nonneg (-1))
          rw [← mul_assoc, ← Real.exp_add, show (-1 : ℝ) + 2 = 1 by norm_num] at h
          exact h
        have hSq : E * (j : ℝ) ^ 2 / k ≤ (j : ℝ) / 2 := by
          have hE' := (div_le_iff₀ hA).1 hLogE
          have ht' : (j : ℝ) * (A * Real.log k) ≤ (k : ℝ) :=
            (le_div_iff₀ (mul_pos hA hL₀)).1 hs
          have h' := (mul_le_mul_of_nonneg_right hE' hj').trans_eq (by ring :
            Real.log k * A * (j : ℝ) = (j : ℝ) * (A * Real.log k))
          apply (div_le_iff₀ hk₀).2
          nlinarith only [mul_le_mul_of_nonneg_right (h'.trans ht') hj']
        have hbound := mul_le_mul
          ((hPow j hju hjk).trans (pow_le_pow_left₀ (by positivity) hBase _))
          (Real.exp_le_exp.mpr hSq) (Real.exp_nonneg _) (by positivity)
        refine hbound.trans ?_
        rw [← Real.exp_nat_mul, ← Real.exp_add,
          show (j : ℝ) * (-1) + (j : ℝ) / 2 = (j : ℝ) * (-(1 / 2)) by ring,
          Real.exp_nat_mul]
        exact (pow_le_pow_left₀ (Real.exp_nonneg _) hHalf _).trans (by linarith only [hQ, hG₂, hG₃])
    · rw [ite_eq_right hs]
      by_cases hjρ : (j : ℝ) ≤ (3 / 4 : ℝ) * k
      · rw [ite_eq_left hjρ]
        have hj₀ : (0 : ℝ) < j := ht₀.trans (lt_of_not_ge hs)
        have hju : 0 < j := by exact_mod_cast hj₀
        have hBase : Real.exp (1 + D) * μ / (j : ℝ) ≤ 1 / 2 := by
          apply (div_le_iff₀ hj₀).2
          have hh : 2 * Real.exp (1 + D) * Real.sqrt k ≤ t := by
            apply (le_div_iff₀ (mul_pos hA hL₀)).2
            have h := mul_le_mul_of_nonneg_right hMid' (Real.sqrt_nonneg k)
            rw [← pow_two, hroot] at h
            exact (by simpa only [mul_assoc, mul_left_comm, mul_comm] using h)
          have hb := (mul_le_mul_of_nonneg_left hμ (show 0 ≤ 2 * Real.exp (1 + D) by positivity)).trans
            (hh.trans (le_of_not_ge hs))
          linarith only [hb]
        calc
          _ ≤ (Real.exp 1 * μ / (j : ℝ)) ^ j * Real.exp (D * (j : ℝ)) :=
            mul_le_mul_of_nonneg_right (hPow j hju hjk) (Real.exp_nonneg _)
          _ = (Real.exp (1 + D) * μ / (j : ℝ)) ^ j := by
            rw [mul_comm D, Real.exp_nat_mul, ← mul_pow, Real.exp_add]
            congr 1
            ring
          _ ≤ (1 / 2 : ℝ) ^ j := pow_le_pow_left₀ (by positivity) hBase _
          _ ≤ _ := by linarith only [hQ, hG₁, hG₃]
      · rw [ite_eq_right hjρ]
        linarith only [hQ, hG₁, hG₂]
  have hSum := Finset.sum_le_sum (s := Finset.range (k + 1)) hPoint
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hPSum, mul_one, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hSum
  have hG₁ := sum_geometric_range_le (show 0 ≤ (2/3:ℝ) by norm_num) (by norm_num) k
  have hG₂ := sum_geometric_range_le (show 0 ≤ (1/2:ℝ) by norm_num) (by norm_num) k
  have hG₃ : (((k + 1 : ℕ) : ℝ) * Real.exp (-(k : ℝ))) ≤ 1 := by
    rw [Nat.cast_add, Nat.cast_one, Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_one (Real.exp_pos _)).2 (by simpa only [add_comm] using Real.add_one_le_exp (k : ℝ))
  norm_num at hG₁ hG₂
  linarith only [hSum, hG₁, hG₂, hG₃]

end BoundedEdgeRegularSubgraphs
