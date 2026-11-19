module

public import BoundedEdgeRegularSubgraphs.NearBalanceTransfer
public import BoundedEdgeRegularSubgraphs.PermutedBlocks
import Mathlib.Tactic

/-!
# Amplification for arrays with nearly equal expected degrees
-/

public section

open Filter MeasureTheory Set Function
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

set_option maxHeartbeats 650000 in
/-- Theorem 4.2. The rate holds uniformly in the array and admissible
orders with the stated maximum imbalance. -/
theorem eventually_exactOrder_failure_le_of_nearBalance {ξ M : ℝ}
    (hξ : 0 < ξ) (hξ₁ : ξ < 1 / 2) (hM : 0 ≤ M) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      (k : ℝ) ≤ a * (n : ℝ) ^ (2 / 3 : ℝ) →
      ∀ q : Edge (Fin n) → Icc (0 : ℝ) 1, HasFloor ξ q →
        (∃ p ∈ Icc ξ (1 - ξ), ∀ i, |degreeSum (fun e ↦ (q e : ℝ)) i / ((n : ℝ) - 1) - p| ≤
          Real.sqrt (M / k)) →
        (graphLaw q).real (exactOrderEvent k)ᶜ ≤
          Real.exp (-c * (n : ℝ) / (k : ℝ) ^ (3 / 2 : ℝ)) := by
  classical
  obtain ⟨H, p₀, hH, hp₀, hp₁, hSuccess⟩ :=
    eventually_exactOrder_success_of_nearBalance hξ hξ₁ (sq_nonneg (Real.sqrt M + 1))
  obtain ⟨a, ha, hScale⟩ := exists_largeCell_blockScale (s := 0) (c₀ := 1) le_rfl (by norm_num) hH
  let c := p₀ / (8 * H)
  have hH₀ : 0 < H := zero_lt_one.trans_le hH
  refine ⟨a, c, ha, by dsimp only [c]; positivity, ?_⟩
  filter_upwards [eventually_regularBlockSize_bounds_half hH, hScale, hSuccess,
    eventually_ge_atTop (1 : ℕ)] with k hkScale hScale' hSucc hk
  intro n hSize q hq hNear
  obtain ⟨p, hp, hNear⟩ := hNear
  let m := regularBlockSize H k
  let v := (Real.sqrt k)⁻¹
  let w := symmetricEdgeWeight (fun e ↦ (q e : ℝ))
  have hm : m ≤ n := by
    have h := hScale' n n (by simpa only [zero_add] using hSize) (by omega)
    have h' : (m : ℝ) ≤ n := by simpa only [Real.rpow_zero, mul_one, one_mul] using h
    exact_mod_cast h'
  have hn : 1 ≤ n := (show 1 ≤ m by omega).trans hm
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hW (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n))) (j : Fin n)
      (hj : j ∈ (Finset.univ : Finset (Fin n)).erase i) : w i j ∈ Icc (0 : ℝ) 1 := by
    rcases lt_or_gt_of_ne (Finset.mem_erase.mp hj).1.symm with h | h
    · rw [show w i j = (q ⟨(i, j), h⟩ : ℝ) from symmetricEdgeWeight_eq_of_lt _ h]
      exact (q _).property
    · rw [show w i j = (q ⟨(j, i), h⟩ : ℝ) from symmetricEdgeWeight_eq_of_gt _ h]
      exact (q _).property
  let A : Finset (Finset (Fin n)) := Finset.univ.powersetCard m
  let Good (S : Finset (Fin n)) : Prop := ∀ i ∈ S, |sampleRowMean S w i - sampleRowMean Finset.univ w i| ≤ v
  have hBad (S : Finset (Fin n)) :
      (∃ i ∈ S, v < |sampleRowMean S w i - sampleRowMean Finset.univ w i|) ↔ ¬ Good S := by
    simp only [Good, not_forall, not_le, exists_prop]
  have hG : n.choose m ≤ 2 * (A.filter Good).card := by
    have hBound := card_samples_rowMean_bad_le (Finset.univ : Finset (Fin n)) w hkScale.1
      (by simpa only [Finset.card_univ, Fintype.card_fin] using hm) hW hv
    simp only [hBad, Finset.card_univ, Fintype.card_fin] at hBound
    have hc : (A.card : ℝ) = (n.choose m : ℝ) := by simp [A]
    have hh : ((A.filter fun S ↦ ¬Good S).card : ℝ) ≤ (A.card : ℝ) / 2 := by
      have hr := mul_le_mul_of_nonneg_left hkScale.2.2.2.le (Nat.cast_nonneg (α := ℝ) (n.choose m))
      have hh' := hBound.trans hr
      rw [← hc] at hh'
      linarith only [hh']
    have hsum : ((A.filter Good).card : ℝ) + ((A.filter fun S ↦ ¬Good S).card : ℝ) = (A.card : ℝ) := by
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
        Finset.sum_filter_add_sum_filter_not A Good (fun _ ↦ (1 : ℝ))
    have h : (n.choose m : ℝ) ≤ 2 * ((A.filter Good).card : ℝ) := by
      linarith only [hh, hsum, hc]
    exact_mod_cast h
  obtain ⟨σ, hσ⟩ := exists_permuted_blocks_half_good n m Good hG
  let b := n / m
  let U (i : Fin b) := (consecutiveVertexBlock n m i).map σ.toEmbedding
  let I := (Finset.univ : Finset (Fin b)).filter fun i ↦ Good (U i)
  have hPair : Pairwise (Disjoint on U) := by
    intro i j h
    exact (Finset.disjoint_map σ.toEmbedding).mpr (pairwise_disjoint_consecutiveVertexBlock n m h)
  have hU (i : Fin b) : (U i).card = m := (Finset.card_map _).trans (card_consecutiveVertexBlock n m i)
  have hLocal (i : I) : p₀ ≤ (graphLaw (induce (U i.val) q)).real (exactOrderEvent k) := by
    have hN : Fintype.card ↥(U i.val) = m := (Fintype.card_coe _).trans (hU i.val)
    have hD : Good (U i.val) := (Finset.mem_filter.mp i.property).2
    have hSize : H * (k : ℝ) * Real.sqrt k ≤ (Fintype.card ↥(U i.val) : ℝ) := by
      rw [hN]
      exact hkScale.2.1
    apply hSucc hSize (induce (U i.val) q) (fun e ↦ hq (inducedEdge _ e))
    refine ⟨p, hp, fun x ↦ ?_⟩
    have hM' : Real.sqrt (M / (k : ℝ)) = Real.sqrt M * v := by
      rw [Real.sqrt_div hM, div_eq_mul_inv]
    rw [sqrt_div_sq_eq_mul_inv_sqrt _ (by positivity)]
    have h := hD x.val x.property
    have h₁ := sampleRowMean_eq_induced_degree q (U i.val) (by rw [hU]; omega) x
    rw [h₁, sampleRowMean_univ_eq_degree _ (by simpa only [Fintype.card_fin] using hn), Fintype.card_fin] at h
    rw [Fintype.card_coe]
    have h₂ := (abs_sub_le (degreeSum (fun e ↦ (induce (U i.val) q e).val) x /
      (((U i.val).card : ℝ) - 1))
      (degreeSum (fun e ↦ (q e : ℝ)) x.val / ((n : ℝ) - 1)) p).trans (add_le_add h (hNear x.val))
    rw [hM'] at h₂
    exact h₂.trans_eq (by dsimp only [v]; ring)
  have hprob := probability_exactOrder_failure_le_of_disjoint_blocks q (fun i : I ↦ U i.val)
    (fun _ _ h ↦ hPair (fun he ↦ h (Subtype.ext he))) k hp₀.le hp₁ hLocal
  rw [Fintype.card_coe] at hprob
  have hb : 1 ≤ b := Nat.le_div_iff_mul_le (by omega : 0 < m) |>.2 (by simpa only [one_mul] using hm)
  have hnB : n ≤ 2 * b * m := by
    have hlt := Nat.lt_div_mul_add (a := n) (by omega : 0 < m)
    have hcmp := Nat.mul_le_mul_right m (show b + 1 ≤ 2 * b by omega)
    exact (by simpa only [Nat.add_mul, one_mul] using hlt.le : n ≤ (b + 1) * m).trans hcmp
  have hCov : (n : ℝ) ≤ 4 * (I.card : ℝ) * (m : ℝ) := by
    have h := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (show b ≤ 2 * I.card from hσ) :
      (b : ℝ) ≤ ↑(2 * I.card)) (by positivity : (0 : ℝ) ≤ m)
    push_cast at h
    have hn' : (n : ℝ) ≤ 2 * (b : ℝ) * (m : ℝ) := by exact_mod_cast hnB
    nlinarith only [h, hn']
  have hCover := hCov.trans (mul_le_mul_of_nonneg_left hkScale.2.2.1 (show 0 ≤ 4 * (I.card : ℝ) by positivity))
  have hk₀ : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hDen : (n : ℝ) / (8 * H * ((k : ℝ) * Real.sqrt k)) ≤ (I.card : ℝ) := by
    apply (div_le_iff₀ (show 0 < 8 * H * ((k : ℝ) * Real.sqrt k) by positivity)).2
    nlinarith only [hCover]
  have hExp := mul_le_mul_of_nonneg_left hDen hp₀.le
  have hEq : p₀ * ((n : ℝ) / (8 * H * ((k : ℝ) * Real.sqrt k))) =
      c * (n : ℝ) / (k : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← mul_sqrt_eq_rpow_three_halves (k : ℝ) hk₀.le]
    dsimp only [c]
    ring
  rw [hEq] at hExp
  exact hprob.trans (Real.exp_le_exp.mpr (by simpa only [neg_mul, neg_div] using neg_le_neg hExp))

/-- The equal-expected-degree specialization in Theorem 1.1(2). -/
theorem theorem1_1_equalDegrees : Theorem1_1_equalDegrees := by
  intro ξ hξ hξ₁
  obtain ⟨a, c, ha, hc, h⟩ := eventually_exactOrder_failure_le_of_nearBalance hξ hξ₁ (M := 0) le_rfl
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (h.and (eventually_ge_atTop (1 : ℕ)))
  refine ⟨a, c, ha, hc, k₀, 2, (hk₀ k₀ le_rfl).2, ?_⟩
  intro n hn k hk hSize q hq hEqual
  let i : Fin n := ⟨0, by omega⟩
  let p := degreeSum (fun e ↦ (q e : ℝ)) i / ((n : ℝ) - 1)
  have hp := (row_density_mem_Icc q (by simpa only [Fintype.card_fin] using hn)
    (fun e ↦ (hq e).1) (fun e ↦ (hq e).2)).2 i
  apply (hk₀ k hk).1 n hSize q hq
  refine ⟨p, by simpa only [Fintype.card_fin] using hp, ?_⟩
  intro j
  rw [hEqual j i]
  simp [p]

end BoundedEdgeRegularSubgraphs
