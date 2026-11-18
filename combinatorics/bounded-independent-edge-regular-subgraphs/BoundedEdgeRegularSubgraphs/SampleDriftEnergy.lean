module

public import BoundedEdgeRegularSubgraphs.SampleDistinguishedVertex
import Mathlib.Tactic

/-!
# Mean-square drift on a uniform sample
-/

public section

open Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [DecidableEq α]

@[expose] noncomputable def sampleRowMean (s : Finset α) (q : α → α → ℝ) (i : α) : ℝ :=
  (∑ j ∈ s.erase i, q i j) / (s.card - 1 : ℕ)

@[expose] noncomputable def sampleRowDrift (S : Finset α) (q : α → α → ℝ) (d : ℝ) (i : α) : ℝ :=
  (∑ j ∈ S.erase i, q i j) - d

/-- The total squared drift over all equally weighted samples is bounded
by the conditional variances and the population mean-square imbalance. -/
theorem sum_sample_row_drift_energy_le (s : Finset α) (q : α → α → ℝ)
    {k : ℕ} (hk : 2 ≤ k) (hks : k ≤ s.card) (p d η : ℝ)
    (hq : ∀ i ∈ s, ∀ j ∈ s.erase i, q i j ∈ Icc (0 : ℝ) 1)
    (hd : |p * ((k - 1 : ℕ) : ℝ) - d| ≤ 1)
    (hη : (∑ i ∈ s, (sampleRowMean s q i - p) ^ 2) ≤ (s.card : ℝ) * η ^ 2) :
    (∑ S ∈ s.powersetCard k, ∑ i ∈ S, sampleRowDrift S q d i ^ 2) ≤
      (s.card.choose k : ℝ) * (2 * (k : ℝ) ^ 2 + 2 * η ^ 2 * (k : ℝ) ^ 3) := by
  classical
  let m := k - 1
  let b := (s.card - 1).choose m
  let a (i : α) := sampleRowMean s q i - p
  let μ (i : α) := (m : ℝ) * sampleRowMean s q i - d
  let f (i : α) (T : Finset α) := ((∑ j ∈ T, q i j) - d) ^ 2
  have hk₀ : 0 < k := by omega
  have hrearrange : (∑ S ∈ s.powersetCard k, ∑ i ∈ S, sampleRowDrift S q d i ^ 2) =
      ∑ i ∈ s, ∑ T ∈ (s.erase i).powersetCard m, f i T :=
    sum_samples_distinguished_vertex s hk₀ f
  rw [hrearrange]
  have hi (i : α) (his : i ∈ s) : (∑ T ∈ (s.erase i).powersetCard m, f i T) ≤
      (b : ℝ) * ((m : ℝ) / 4 + 2 + 2 * (m : ℝ) ^ 2 * a i ^ 2) := by
    let X := (s.erase i).powersetCard m
    let D (T : Finset α) := (∑ j ∈ T, q i j) - (m : ℝ) * sampleRowMean s q i
    have hc : (s.erase i).card = s.card - 1 := Finset.card_erase_of_mem his
    have hc' : X.card = b := by simp only [X, Finset.card_powersetCard, hc, b]
    have hm : 0 < (s.erase i).card := by rw [hc]; omega
    have h := sample_deviation_moments (s.erase i) (q i) hm (hq i his) m
    dsimp only at h
    rw [hc] at h
    have hsum : (∑ T ∈ X, D T) = 0 := h.1
    have hsq : (∑ T ∈ X, D T ^ 2) ≤ (b : ℝ) * ((m : ℝ) / 4) := h.2
    have hsplit (T : Finset α) : f i T = D T ^ 2 + 2 * μ i * D T + μ i ^ 2 := by
      dsimp only [f, D, μ]
      ring
    have hμ : μ i ^ 2 ≤ 2 + 2 * (m : ℝ) ^ 2 * a i ^ 2 := by
      have hd' := pow_le_pow_left₀ (abs_nonneg _) hd 2
      rw [sq_abs, one_pow] at hd'
      have hsplit' : μ i = (m : ℝ) * a i + (p * (m : ℝ) - d) := by
        dsimp only [μ, a]
        ring
      have h := sq_nonneg ((m : ℝ) * a i - (p * (m : ℝ) - d))
      rw [hsplit']
      nlinarith only [hd', h]
    change (∑ T ∈ X, f i T) ≤ _
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul, hc']
    have hh := mul_le_mul_of_nonneg_left hμ (Nat.cast_nonneg b : (0 : ℝ) ≤ b)
    linarith only [hsq, hh]
  refine (Finset.sum_le_sum hi).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  have h₀ := mul_le_mul_of_nonneg_left hη (show 0 ≤ 2 * (m : ℝ) ^ 2 by positivity)
  have hb₀ : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hc : (b : ℝ) * (s.card : ℝ) = (s.card.choose k : ℝ) * k := by
    have h := card_mul_choose_pred s hk₀
    have h' : (k : ℝ) * (s.card.choose k : ℝ) = (s.card : ℝ) * (b : ℝ) := by exact_mod_cast h
    linarith only [h']
  have hmK : (m : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  calc
    _ ≤ (b : ℝ) * ((s.card : ℝ) * ((m : ℝ) / 4 + 2) +
        2 * (m : ℝ) ^ 2 * ((s.card : ℝ) * η ^ 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add_right h₀ _) hb₀
    _ = ((b : ℝ) * (s.card : ℝ)) * ((m : ℝ) / 4 + 2 + 2 * (m : ℝ) ^ 2 * η ^ 2) := by ring
    _ = _ * ((k : ℝ) * ((m : ℝ) / 4 + 2 + 2 * (m : ℝ) ^ 2 * η ^ 2)) := by rw [hc]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have hm2 := pow_le_pow_left₀ (Nat.cast_nonneg m : (0 : ℝ) ≤ m) hmK 2
      have hi' := mul_le_mul_of_nonneg_right hm2 (show 0 ≤ 2 * η ^ 2 by positivity)
      have hj : (m : ℝ) / 4 + 2 ≤ 2 * (k : ℝ) := by linarith only [hmK, hkr]
      have hb := mul_le_mul_of_nonneg_left (add_le_add hj
        (show 2 * (m : ℝ) ^ 2 * η ^ 2 ≤ 2 * (k : ℝ) ^ 2 * η ^ 2 by linarith only [hi']))
        (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      nlinarith only [hb]

end BoundedEdgeRegularSubgraphs
