module

public import BoundedEdgeRegularSubgraphs.RegularAtomUpper
import BoundedEdgeRegularSubgraphs.MeanDrift
import Mathlib.Tactic

/-!
# The surplus calculation for a density increment
-/

@[expose] public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- Density of the weighted complete edge array. -/
noncomputable def arrayDensity (q : Edge α → Set.Icc (0 : ℝ) 1) : ℝ :=
  2 * (∑ e : Edge α, (q e : ℝ)) / ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1))

/-- Degree variance in the normalization used for the density increment. -/
noncomputable def normalizedDegreeVariation (q : Edge α → Set.Icc (0 : ℝ) 1) : ℝ :=
  degreeVariation q / (Fintype.card α : ℝ) ^ 3

/-- The vertex bias used in the proof of Lemma 5.1. -/
noncomputable def vertexSelectionWeight (q : Edge α → Set.Icc (0 : ℝ) 1) (i : α) : ℝ :=
  1 / 2 + ((degreeSum (fun e ↦ (q e : ℝ)) i -
    vertexMean (degreeSum (fun e ↦ (q e : ℝ)))) / Fintype.card α) / 4

theorem sum_edge_endpoint_values (v : α → ℝ) :
    (∑ e : Edge α, (v e.val.1 + v e.val.2)) =
      ((Fintype.card α : ℝ) - 1) * ∑ i, v i := by
  have h := weighted_degree_sum (fun _ : Edge α ↦ 1) v
  simp_rw [degreeSum_one, mul_one, ← Finset.sum_mul] at h
  rw [← h]
  ring

theorem card_edge_twice :
    (2 : ℝ) * (Fintype.card (Edge α) : ℝ) =
      (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) := by
  have h := sum_edge_endpoint_values (fun _ : α ↦ (1 : ℝ))
  norm_num only [Nat.reduceAdd, one_add_one_eq_two, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at h
  simpa only [mul_comm] using h

/-- The expected density surplus of the biased sample in Lemma 5.1,
computed from its independent inclusion probabilities. -/
theorem density_increment_weighted_surplus (q : Edge α → Set.Icc (0 : ℝ) 1)
    (hn : 2 ≤ Fintype.card α) :
    (Fintype.card α : ℝ) ^ 2 * normalizedDegreeVariation q / 32 ≤
      ∑ e : Edge α, ((q e : ℝ) - (arrayDensity q + normalizedDegreeVariation q / 2)) *
        (vertexSelectionWeight q e.val.1 * vertexSelectionWeight q e.val.2) := by
  let n : ℝ := Fintype.card α
  have hn₂ : (2 : ℝ) ≤ n := by dsimp only [n]; exact_mod_cast hn
  have hn₀ : 0 < n := by linarith
  let μ := degreeSum (fun e ↦ (q e : ℝ))
  let a (i : α) := (μ i - vertexMean μ) / n
  let B := ∑ i, a i ^ 2
  let Q := ∑ e : Edge α, (q e : ℝ)
  let w := vertexSelectionWeight q
  let p := arrayDensity q
  let v := normalizedDegreeVariation q
  have ha : (∑ i, a i) = 0 := by
    dsimp only [a]
    rw [← Finset.sum_div, sum_sub_vertexMean, zero_div]
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hnB : n * v = B := by
    dsimp only [v, normalizedDegreeVariation, degreeVariation, B, a]
    simp_rw [div_pow]
    rw [← Finset.sum_div]
    field_simp
    rfl
  have hv : 0 ≤ v := nonneg_of_mul_nonneg_right (hnB ▸ hB) hn₀
  have hp : 0 ≤ p :=
    div_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun e _ ↦ (q e).property.1)))
      (mul_nonneg hn₀.le (by linarith))
  have hw (i : α) : w i = 1 / 2 + a i / 4 := rfl
  have hcov : ∑ i, a i * μ i = n * B := by
    have h (i : α) : a i * μ i = n * a i ^ 2 + a i * vertexMean μ := by
      dsimp only [a]
      field_simp
      ring
    simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ha, zero_mul, add_zero]
    rfl
  have htotal : ∑ e : Edge α, (a e.val.1 + a e.val.2) = 0 := by
    rw [sum_edge_endpoint_values, ha, mul_zero]
  have hqtotal : ∑ e : Edge α, (q e : ℝ) * (a e.val.1 + a e.val.2) = n * B := by
    simp_rw [mul_comm (q _ : ℝ)]
    rw [← weighted_degree_sum, hcov]
  have hsquares : ∑ e : Edge α, ((a e.val.1) ^ 2 + (a e.val.2) ^ 2) = (n - 1) * B :=
    sum_edge_endpoint_values (fun i ↦ a i ^ 2)
  have hpair : (∑ e : Edge α, a e.val.1 * a e.val.2) = -B / 2 := by
    have hh := sum_edge_squares a
    rw [ha, zero_pow (by decide), add_zero] at hh
    have hsum : (∑ e : Edge α, (a e.val.1 + a e.val.2) ^ 2) =
        (n - 1) * B + 2 * ∑ e : Edge α, a e.val.1 * a e.val.2 := by
      rw [← hsquares, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun e _ ↦ by ring)
    rw [hsum] at hh
    change _ = (n - 2) * B at hh
    linarith only [hh]
  have hweighted : -(n * B) / 2 ≤ ∑ e : Edge α, (q e : ℝ) * a e.val.1 * a e.val.2 := by
    have h (e : Edge α) : -((a e.val.1) ^ 2 + (a e.val.2) ^ 2) / 2 ≤
        (q e : ℝ) * a e.val.1 * a e.val.2 := by
      have hs : -((a e.val.1) ^ 2 + (a e.val.2) ^ 2) / 2 ≤ a e.val.1 * a e.val.2 :=
        by nlinarith only [sq_nonneg (a e.val.1 + a e.val.2)]
      have ht := mul_le_mul_of_nonneg_left hs (q e).property.1
      have hp := mul_nonneg (sub_nonneg.mpr (q e).property.2)
        (add_nonneg (sq_nonneg (a e.val.1)) (sq_nonneg (a e.val.2)))
      nlinarith only [ht, hp]
    have hh := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) ↦ h e)
    rw [← Finset.sum_div, Finset.sum_neg_distrib, hsquares] at hh
    linarith only [hh, hB]
  have hmass : ∑ e : Edge α, w e.val.1 * w e.val.2 =
      n * (n - 1) / 8 - B / 32 := by
    have hh (e : Edge α) : w e.val.1 * w e.val.2 =
      1 / 4 + (a e.val.1 + a e.val.2) / 8 + (a e.val.1 * a e.val.2) / 16 := by
      rw [hw, hw]
      ring
    simp_rw [hh, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, htotal, hpair]
    have hc := card_edge_twice (α := α)
    change 2 * (Fintype.card (Edge α) : ℝ) = n * (n - 1) at hc
    linarith only [hc]
  have hmassW : Q / 4 + 3 * n * B / 32 ≤
      ∑ e : Edge α, (q e : ℝ) * (w e.val.1 * w e.val.2) := by
    have hh (e : Edge α) : (q e : ℝ) * (w e.val.1 * w e.val.2) =
      (q e : ℝ) / 4 + (q e : ℝ) * (a e.val.1 + a e.val.2) / 8 +
        (q e : ℝ) * a e.val.1 * a e.val.2 / 16 := by
      rw [hw, hw]
      ring
    simp_rw [hh, Finset.sum_add_distrib, ← Finset.sum_div, hqtotal]
    change Q / 4 + 3 * n * B / 32 ≤ _
    linarith only [hweighted]
  have hbase : p * (n * (n - 1) / 8) = Q / 4 := by
    have hne : n - 1 ≠ 0 := by linarith
    dsimp only [p, arrayDensity]
    change (2 * Q / (n * (n - 1))) * (n * (n - 1) / 8) = Q / 4
    field_simp
    ring
  have hbind : (p + v / 2) * (B / 32) ≥ 0 := by positivity
  have hfact : -(v / 2 * (n * (n - 1) / 8)) =
      -(n * B) / 16 + B / 16 := by rw [← hnB]; ring
  change n ^ 2 * v / 32 ≤ ∑ e : Edge α, ((q e : ℝ) - (p + v / 2)) *
    (w e.val.1 * w e.val.2)
  simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hmass]
  have hleft : n ^ 2 * v / 32 = n * B / 32 := by rw [← hnB]; ring
  rw [hleft]
  nlinarith only [hmassW, hbase, hbind, hfact, hB]

end BoundedEdgeRegularSubgraphs
