module

public import BoundedEdgeRegularSubgraphs.OrderUpper
import BoundedEdgeRegularSubgraphs.MeanDrift
import Mathlib.Tactic

/-!
# Degree variation in the rank-one model
-/

public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The expected degree in a product array is the vertex weight times the
sum of the weights of its other vertices. -/
theorem degreeSum_product (z : α → ℝ) (i : α) :
    degreeSum (fun e ↦ z e.val.1 * z e.val.2) i = z i * ((∑ j, z j) - z i) := by
  classical
  let N := (Finset.univ : Finset α).erase i
  let edge (j : α) (hj : j ∈ N) : Edge α := if h : j < i then ⟨(j, i), h⟩ else
    ⟨(i, j), (lt_or_gt_of_ne (Finset.ne_of_mem_erase hj)).resolve_left h⟩
  have hsum : (∑ j ∈ N, z i * z j) =
      z i * ((∑ j, z j) - z i) := by
    rw [← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  rw [← hsum]
  unfold degreeSum
  rw [← Finset.sum_filter]
  symm
  let other (e : Edge α) := if i = e.val.1 then e.val.2 else e.val.1
  refine Finset.sum_bij' edge (fun e _ ↦ other e) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    have hne : j ≠ i := Finset.ne_of_mem_erase hj
    rcases lt_or_gt_of_ne hne with h | h
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, Or.inr (by simp [edge, h])⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, Or.inl (by simp [edge, not_lt_of_gt h])⟩
  · intro e he
    have he' := (Finset.mem_filter.mp he).2
    rcases he' with hi | hi
    · simp [N, other, hi, ne_of_gt e.property]
    · simp [N, other, hi, ne_of_gt e.property, ne_of_lt e.property]
  · intro j hj
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with h | h
    · simp [other, edge, h, ne_of_gt h]
    · simp [other, edge, not_lt_of_gt h]
  · intro e he
    obtain hi | hi := (Finset.mem_filter.mp he).2
    · apply Subtype.ext
      simp [other, edge, hi, not_lt_of_gt e.property]
    · apply Subtype.ext
      simp [other, edge, hi, e.property, ne_of_gt e.property]
  · intro j hj
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with h | h
    · simp [edge, h, mul_comm]
    · simp [edge, not_lt_of_gt h]

omit [LinearOrder α] in
private theorem sum_pair_sq (u : α → ℝ) :
    (∑ i, ∑ j, (u i - u j) ^ 2) =
      2 * (Fintype.card α : ℝ) * ∑ i, (u i - vertexMean u) ^ 2 := by
  let v : α → ℝ := fun i ↦ u i - vertexMean u
  have hv : ∑ i, v i = 0 := sum_sub_vertexMean u
  have hdiff (i j : α) : (u i - u j) ^ 2 = v i ^ 2 + v j ^ 2 - 2 * v i * v j := by
    dsimp [v]
    ring
  simp_rw [hdiff, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hv, mul_zero, Finset.sum_const_zero, sub_zero]
  rw [← Finset.mul_sum]
  ring

omit [LinearOrder α] in
private theorem sum_squares_anchor (u : α → ℝ) (hn : 0 < Fintype.card α) :
    ∃ i, ∑ j, (u j - u i) ^ 2 ≤ 2 * ∑ j, (u j - vertexMean u) ^ 2 := by
  by_contra! h
  have : Nonempty α := Fintype.card_pos_iff.mp hn
  have ht := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ ↦ h i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at ht
  rw [Finset.sum_comm, sum_pair_sq] at ht
  linarith

/-- For a product law the difference in row sums factors into the difference
of the two vertex weights and the sum of the other weights. -/
theorem degreeSum_product_sub (z : α → ℝ) (i j : α) :
    degreeSum (fun e ↦ z e.val.1 * z e.val.2) i -
      degreeSum (fun e ↦ z e.val.1 * z e.val.2) j =
        (z i - z j) * ((∑ l, z l) - z i - z j) := by
  rw [degreeSum_product, degreeSum_product]
  ring

/-- Variance lower bound for a product array with separated vertex weights. -/
theorem degreeVariation_product_anchor (hk : 3 ≤ Fintype.card α)
    (p : Edge α → Set.Icc (0 : ℝ) 1) (z x : α → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : ∀ i, a ≤ z i)
    (hp : ∀ e, (p e : ℝ) = z e.val.1 * z e.val.2)
    (hsep : ∀ i j, b * |x i - x j| ≤ |z i - z j|) :
    ∃ v : α, (a * b) ^ 2 * ((Fintype.card α : ℝ) - 2) ^ 2 *
      (∑ i, (x i - x v) ^ 2) ≤ 2 * degreeVariation p := by
  classical
  let k : ℝ := Fintype.card α
  let μ := degreeSum (fun e ↦ (p e : ℝ))
  let coef := (a * b) ^ 2 * (k - 2) ^ 2
  have hk' : (3 : ℝ) ≤ k := by dsimp only [k]; exact_mod_cast hk
  have hk₀ : 0 < k := by linarith
  have hcoef : 0 ≤ coef := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hother (i j : α) (hij : i ≠ j) : a * (k - 2) ≤ (∑ l, z l) - z i - z j := by
    let T := ((Finset.univ : Finset α).erase i).erase j
    have hj : j ∈ (Finset.univ : Finset α).erase i := by simp [hij.symm]
    have hcard : (T.card : ℝ) = k - 2 := by
      dsimp only [T, k]
      rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Nat.sub_sub, Nat.cast_sub (by omega : 2 ≤ Fintype.card α)]
      norm_num
    calc
      a * (k - 2) = ∑ _ ∈ T, a := by rw [Finset.sum_const, nsmul_eq_mul, hcard, mul_comm]
      _ ≤ ∑ l ∈ T, z l := Finset.sum_le_sum (fun i _ ↦ hz i)
      _ = _ := by
        dsimp only [T]
        rw [Finset.sum_erase_eq_sub hj, Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  have hp' : (fun e ↦ (p e : ℝ)) = fun e ↦ z e.val.1 * z e.val.2 := funext hp
  have hpair (i j : α) : coef * (x i - x j) ^ 2 ≤ (μ i - μ j) ^ 2 := by
    by_cases hij : i = j
    · subst j
      simp
    have hn : 0 ≤ a * (k - 2) := mul_nonneg ha (by linarith)
    let r := (∑ l, z l) - z i - z j
    have hr : 0 ≤ r := hn.trans (hother i j hij)
    have hh : (a * (k - 2)) * (b * |x i - x j|) ≤ |μ i - μ j| := by
      have hprod := mul_le_mul (hother i j hij) (hsep i j)
        (mul_nonneg hb (abs_nonneg _)) hr
      dsimp only [μ]
      rw [hp', degreeSum_product_sub, abs_mul, abs_of_nonneg hr, mul_comm (|z i - z j|)]
      exact hprod
    have hs := (sq_le_sq₀ (by positivity : 0 ≤ (a * (k - 2)) * (b * |x i - x j|))
      (abs_nonneg _)).mpr hh
    rw [sq_abs, mul_pow, mul_pow, mul_pow, sq_abs] at hs
    dsimp only [coef]
    nlinarith only [hs]
  obtain ⟨v, hv⟩ := sum_squares_anchor x (by omega)
  refine ⟨v, ?_⟩
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) ↦ hpair i j))
  simp_rw [← Finset.mul_sum, sum_pair_sq] at hsum
  have hvar : coef * (∑ i, (x i - vertexMean x) ^ 2) ≤ degreeVariation p := by
    apply le_of_mul_le_mul_left _ (show 0 < 2 * k by positivity)
    dsimp only [degreeVariation]
    change (2 * k) * (coef * ∑ i, (x i - vertexMean x) ^ 2) ≤
      (2 * k) * ∑ i, (μ i - vertexMean μ) ^ 2
    calc
      _ = coef * (2 * (Fintype.card α : ℝ) * ∑ i, (x i - vertexMean x) ^ 2) :=
        mul_left_comm (2 * k) coef _
      _ ≤ _ := hsum
  exact (mul_le_mul_of_nonneg_left hv hcoef).trans (by linarith only [hvar])


end BoundedEdgeRegularSubgraphs
