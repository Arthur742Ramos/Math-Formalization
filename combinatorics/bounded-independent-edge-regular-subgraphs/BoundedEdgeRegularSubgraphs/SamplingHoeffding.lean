module

public import BoundedEdgeRegularSubgraphs.SymmetricMean
public import BoundedEdgeRegularSubgraphs.Tilt
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-!
# Exponential bounds for a uniform sample without replacement
-/

public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [DecidableEq α]

private theorem exp_mul_le_chord (x u : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (u * x) ≤ 1 - x + x * Real.exp u := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ u)
    (sub_nonneg.mpr hx.2) hx.1 (show 1 - x + x = 1 by ring)
  simpa only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one, mul_comm u x] using h

omit [DecidableEq α] in
private theorem average_exp_centered_le (s : Finset α) (x : α → ℝ) (hs : 0 < s.card)
    (hx : ∀ i ∈ s, x i ∈ Set.Icc (0 : ℝ) 1) (u : ℝ) :
    let a := (∑ i ∈ s, x i) / (s.card : ℝ)
    (∑ i ∈ s, Real.exp (u * (x i - a))) / (s.card : ℝ) ≤ Real.exp (u ^ 2 / 8) := by
  intro a
  have hn : 0 < (s.card : ℝ) := Nat.cast_pos.mpr hs
  have ha₀ : 0 ≤ a := div_nonneg (Finset.sum_nonneg (fun i hi ↦ (hx i hi).1)) hn.le
  have ha₁ : a ≤ 1 := by
    apply (div_le_one hn).mpr
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
      (Finset.sum_le_sum (fun i hi ↦ (hx i hi).2))
  let q : Set.Icc (0 : ℝ) 1 := ⟨a, ha₀, ha₁⟩
  have hsum : (∑ i ∈ s, x i) = (s.card : ℝ) * a := by
    dsimp [a]
    field_simp
  have hchord : (∑ i ∈ s, Real.exp (u * x i)) / (s.card : ℝ) ≤ tiltNormalizer q u := by
    apply (div_le_iff₀ hn).mpr
    calc
      _ ≤ ∑ i ∈ s, (1 - x i + x i * Real.exp u) :=
        Finset.sum_le_sum (fun i hi ↦ exp_mul_le_chord (x i) u (hx i hi))
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one, tiltNormalizer, q]
        ring
  have hmgf := Real.exp_le_exp.mpr (logTiltNormalizer_sub_le q u)
  have he : Real.exp (Real.log (tiltNormalizer q u) - (q : ℝ) * u) =
      Real.exp (-u * a) * tiltNormalizer q u := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (tiltNormalizer_pos _ _)]
    change tiltNormalizer q u * Real.exp (-(a * u)) = _
    rw [mul_comm a u, ← neg_mul, mul_comm]
  rw [he] at hmgf
  calc
    _ = Real.exp (-u * a) * ((∑ i ∈ s, Real.exp (u * x i)) / (s.card : ℝ)) := by
      have hpt (i : α) : Real.exp (u * (x i - a)) = Real.exp (-u * a) * Real.exp (u * x i) := by
        rw [← Real.exp_add]
        congr 1
        ring
      simp_rw [hpt]
      rw [← Finset.mul_sum, mul_div_assoc]
    _ ≤ _ := (mul_le_mul_of_nonneg_left hchord (Real.exp_nonneg _)).trans hmgf

/-- The centred exponential moment of the sum of a uniform sample is at
most the bound for independent draws from the same population. -/
theorem sum_exp_sample_deviation_le (s : Finset α) (x : α → ℝ)
    (hs : 0 < s.card) (hx : ∀ i ∈ s, x i ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) (u : ℝ) :
    let a := (∑ i ∈ s, x i) / (s.card : ℝ)
    (∑ t ∈ s.powersetCard k, Real.exp (u * ((∑ i ∈ t, x i) - (k : ℝ) * a))) ≤
      (s.card.choose k : ℝ) * Real.exp ((k : ℝ) * u ^ 2 / 8) := by
  intro a
  let z (i : α) := Real.exp (u * (x i - a))
  have hz (i : α) : 0 ≤ z i := Real.exp_nonneg _
  have he : (∑ t ∈ s.powersetCard k, Real.exp (u * ((∑ i ∈ t, x i) - (k : ℝ) * a))) =
      ∑ t ∈ s.powersetCard k, ∏ i ∈ t, z i := by
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [z]
    rw [← Real.exp_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, (Finset.mem_powersetCard.mp ht).2]
  rw [he]
  refine (sum_powersetCard_prod_le_choose_mean_pow s z (fun i _ ↦ hz i) k).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [show (k : ℝ) * u ^ 2 / 8 = k * (u ^ 2 / 8) by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (div_nonneg (Finset.sum_nonneg (fun i _ ↦ hz i)) (Nat.cast_nonneg _))
    (average_exp_centered_le s x hs hx u) _

/-- The upper Hoeffding tail in Lemma 2.2, expressed as a count of samples. -/
theorem card_sample_upper_deviation_le (s : Finset α) (x : α → ℝ)
    (hs : 0 < s.card) (hx : ∀ i ∈ s, x i ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    let a := (∑ i ∈ s, x i) / (s.card : ℝ)
    (((s.powersetCard k).filter fun t ↦ (k : ℝ) * ε ≤
      (∑ i ∈ t, x i) - (k : ℝ) * a).card : ℝ) ≤
        (s.card.choose k : ℝ) * Real.exp (-2 * (k : ℝ) * ε ^ 2) := by
  classical
  intro a
  let u := 4 * ε
  have hu : 0 ≤ u := by dsimp [u]; positivity
  let F (t : Finset α) := Real.exp (u * ((∑ i ∈ t, x i) - (k : ℝ) * a))
  let B := (s.powersetCard k).filter fun t ↦ (k : ℝ) * ε ≤
    (∑ i ∈ t, x i) - (k : ℝ) * a
  have hB : (B.card : ℝ) * Real.exp (u * ((k : ℝ) * ε)) ≤
      (s.card.choose k : ℝ) * Real.exp ((k : ℝ) * u ^ 2 / 8) := by
    calc
      _ = ∑ _ ∈ B, Real.exp (u * ((k : ℝ) * ε)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ t ∈ B, F t := by
        apply Finset.sum_le_sum
        intro t ht
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp ht).2 hu)
      _ ≤ ∑ t ∈ s.powersetCard k, F t :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ ↦ Real.exp_nonneg _)
      _ ≤ _ := sum_exp_sample_deviation_le s x hs hx k u
  have hB' := (le_div_iff₀ (Real.exp_pos (u * ((k : ℝ) * ε)))).2 hB
  rw [mul_div_assoc, ← Real.exp_sub] at hB'
  have he : (k : ℝ) * u ^ 2 / 8 - u * ((k : ℝ) * ε) = -2 * (k : ℝ) * ε ^ 2 := by dsimp [u]; ring
  rwa [he] at hB'

end BoundedEdgeRegularSubgraphs
