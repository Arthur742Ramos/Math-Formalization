module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Analysis.Complex.Exponential
import BoundedEdgeRegularSubgraphs.OrderUpper
import Mathlib.Tactic

/-!
# Intersections of uniformly sampled sets
-/

public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

private theorem choose_ratio_le {N k j : ℕ} (hj : j ≤ k) (hk : k ≤ N)
    (hN : 0 < N) :
    (k.choose j : ℝ) / (N.choose j : ℝ) ≤ ((k : ℝ) / N) ^ j := by
  have hd (n : ℕ) : (n.descFactorial j : ℝ) =
      (j.factorial : ℝ) * (n.choose j : ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose n j
  have hf : (j.factorial : ℝ) ≠ 0 := by positivity
  calc
    _ = (k.descFactorial j : ℝ) / (N.descFactorial j : ℝ) := by
      rw [hd, hd, mul_div_mul_left _ _ hf]
    _ = ∏ h ∈ Finset.range j, ((k - h : ℕ) : ℝ) / ((N - h : ℕ) : ℝ) := by
      simp only [Nat.descFactorial_eq_prod_range, Nat.cast_prod, Finset.prod_div_distrib]
    _ ≤ ∏ _ ∈ Finset.range j, (k : ℝ) / N := by
      apply Finset.prod_le_prod₀ (fun h _ ↦ by positivity)
      intro h hh
      have h' := Finset.mem_range.mp hh
      have hhk : h ≤ k := h'.le.trans hj
      have hhN : h < N := h'.trans_le (hj.trans hk)
      rw [Nat.cast_sub hhk, Nat.cast_sub hhN.le]
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have hdiff : (0 : ℝ) < (N : ℝ) - h :=
        sub_pos.mpr (by exact_mod_cast hhN)
      apply (div_le_div_iff₀ hdiff hN').2
      nlinarith only [mul_nonneg (show (0 : ℝ) ≤ h by positivity)
        (sub_nonneg.mpr (show (k : ℝ) ≤ N by exact_mod_cast hk))]
    _ = _ := by simp only [Finset.prod_const, Finset.card_range]

variable {α : Type*} [DecidableEq α]

/-- A prescribed `j`-set belongs to at most a `(k/N)^j` fraction of
the `k`-subsets of an `N`-element population. -/
theorem card_sample_containing_le (s J : Finset α) {k : ℕ}
    (hs : 0 < s.card) (hJs : J ⊆ s) (hJ : J.card ≤ k) (hk : k ≤ s.card) :
    (((s.powersetCard k).filter (J ⊆ ·)).card : ℝ) ≤
      (s.card.choose k : ℝ) * ((k : ℝ) / s.card) ^ J.card := by
  rw [Finset.card_filter_powersetCard_subset J s k hJs hJ]
  have hc : 0 < (s.card.choose J.card : ℝ) := by
    exact_mod_cast Nat.choose_pos (hJ.trans hk)
  have hm : (s.card.choose k : ℝ) * (k.choose J.card : ℝ) =
      (s.card.choose J.card : ℝ) *
        ((s.card - J.card).choose (k - J.card) : ℝ) := by
    exact_mod_cast Nat.choose_mul (n := s.card) hJ
  calc
    _ = (s.card.choose k : ℝ) * ((k.choose J.card : ℝ) / (s.card.choose J.card : ℝ)) := by
      rw [← mul_div_assoc, hm, mul_comm (s.card.choose J.card : ℝ), mul_div_cancel_right₀ _ hc.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left (choose_ratio_le hJ hk hs) (by positivity)

/-- Both bounds in (3.2), in counting form. Dividing by the number of
samples gives the probability for a uniform sample. -/
theorem card_sample_intersection_eq_le (s S : Finset α) {k j : ℕ}
    (hS : S ⊆ s) (hcard : S.card = k) (hj : 0 < j) (hjk : j ≤ k) :
    let μ := (k : ℝ) ^ 2 / s.card
    (((s.powersetCard k).filter fun T ↦ (S ∩ T).card = j).card : ℝ) ≤
      (s.card.choose k : ℝ) * min (μ ^ j) ((Real.exp 1 * μ / j) ^ j) := by
  classical
  intro μ
  let U := (s.powersetCard k).filter fun T ↦ (S ∩ T).card = j
  let V := (S.powersetCard j).sigma fun J ↦ (s.powersetCard k).filter (J ⊆ ·)
  have hUV : U.card ≤ V.card := by
    apply Finset.card_le_card_of_injOn (fun T ↦ ⟨S ∩ T, T⟩)
    · intro T hT
      obtain ⟨hTs, hTJ⟩ := Finset.mem_filter.mp hT
      exact Finset.mem_sigma.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_left, hTJ⟩,
          Finset.mem_filter.mpr ⟨hTs, Finset.inter_subset_right⟩⟩
    · intro T _ T' _ h
      exact congrArg (fun x : (_ : Finset α) × Finset α ↦ x.2) h
  have hk : k ≤ s.card := hcard ▸ Finset.card_le_card hS
  have hs : 0 < s.card := (hj.trans_le hjk).trans_le hk
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs
  have hν : (0 : ℝ) ≤ ((k : ℝ) / s.card) ^ j := by positivity
  have hcount : (U.card : ℝ) ≤ (s.card.choose k : ℝ) *
      (k.choose j : ℝ) * ((k : ℝ) / s.card) ^ j := by
    apply (show (U.card : ℝ) ≤ V.card by exact_mod_cast hUV).trans
    simp only [V, Finset.card_sigma, Nat.cast_sum]
    calc
      _ ≤ ∑ J ∈ S.powersetCard j,
          ((s.card.choose k : ℝ) * ((k : ℝ) / s.card) ^ j) := by
        apply Finset.sum_le_sum
        intro J hJ
        obtain ⟨hJS, hJj⟩ := Finset.mem_powersetCard.mp hJ
        simpa only [hJj] using card_sample_containing_le s J hs (hJS.trans hS)
          (hJj ▸ hjk) hk
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, hcard]
        ring
  refine hcount.trans ?_
  rw [mul_assoc, mul_min_of_nonneg _ _ (by positivity)]
  apply le_min
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      _ ≤ (k : ℝ) ^ j * ((k : ℝ) / s.card) ^ j :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_pow k j) hν
      _ = μ ^ j := by rw [← mul_pow]; congr 1; dsimp only [μ]; ring
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hfac : ((j : ℝ) / Real.exp 1) ^ j ≤ (j.factorial : ℝ) :=
      exp_pow_le_factorial j hj
    calc
      _ ≤ ((k : ℝ) ^ j / (j.factorial : ℝ)) * ((k : ℝ) / s.card) ^ j :=
        mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div j k) hν
      _ ≤ ((k : ℝ) ^ j / ((j : ℝ) / Real.exp 1) ^ j) * ((k : ℝ) / s.card) ^ j := by
        gcongr
      _ = _ := by
        rw [← div_pow, ← mul_pow]
        congr 1
        dsimp only [μ]
        have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
        field_simp

end BoundedEdgeRegularSubgraphs
