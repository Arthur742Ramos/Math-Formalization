module

public import BoundedEdgeRegularSubgraphs.Theorem11
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

/-!
# The cube cells used for Lipschitz kernels
-/

public section

open Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- One fibre of a finite classification contains at least the average
number of elements per class. -/
theorem exists_average_size_fiber {α β : Type*} [Fintype β] [Nonempty β]
    [DecidableEq β] (S : Finset α) (f : α → β) :
    ∃ b : β, (S.card : ℝ) / Fintype.card β ≤ ((S.filter fun x ↦ f x = b).card : ℝ) := by
  have hcard : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  let a : ℝ := (S.card : ℝ) / Fintype.card β
  have h : (Finset.univ : Finset β).card • a ≤ ∑ x ∈ S, (1 : ℝ) := by
    simp only [Finset.card_univ, nsmul_eq_mul, Finset.sum_const, mul_one, a]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hcard.ne']
  obtain ⟨b, _, hb⟩ :=
    Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (f := f)
      (fun _ _ ↦ Finset.mem_univ _) Finset.univ_nonempty h
  exact ⟨b, by simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hb⟩

/-- Points in a finite cube admit a large cell whose coordinate diameter is
at most the prescribed width. Clipped values of the floor code outside the
input set do not affect its fibres. -/
theorem exists_large_cube_cell {α : Type*} [DecidableEq α] {d : ℕ}
    (S : Finset α) (x : α → Fin d → ℝ) {l u h : ℝ}
    (hlu : l ≤ u) (hh : 0 < h) (hx : ∀ a ∈ S, ∀ j, x a j ∈ Icc l u) :
    ∃ T ⊆ S, (S.card : ℝ) / ((u - l) / h + 1) ^ d ≤ T.card ∧
      ∀ a ∈ T, ∀ b ∈ T, ∀ j, |x a j - x b j| ≤ h := by
  let m : ℕ := ⌊(u - l) / h⌋₊ + 1
  let code (a : α) (j : Fin d) : Fin m :=
    ⟨min ⌊(x a j - l) / h⌋₊ (m - 1), by have : 0 < m := Nat.succ_pos _; omega⟩
  have hc (a : α) (ha : a ∈ S) (j : Fin d) : (code a j).val = ⌊(x a j - l) / h⌋₊ := by
    change min _ (m - 1) = _
    apply min_eq_left
    exact Nat.floor_mono (div_le_div_of_nonneg_right (sub_le_sub_right (hx a ha j).2 l) hh.le)
  have : Nonempty (Fin m) := ⟨⟨0, Nat.succ_pos _⟩⟩
  obtain ⟨c, hcsize⟩ := exists_average_size_fiber S code
  let T := S.filter (fun a ↦ code a = c)
  refine ⟨T, Finset.filter_subset _ _, ?_, ?_⟩
  · have hm : (m : ℝ) ≤ (u - l) / h + 1 := by
      dsimp only [m]
      rw [Nat.cast_add, Nat.cast_one]
      linarith only [Nat.floor_le (div_nonneg (sub_nonneg.mpr hlu) hh.le)]
    have hm₀ : (0 : ℝ) < m := by exact_mod_cast Nat.succ_pos (⌊(u - l) / h⌋₊)
    have hD : (0 : ℝ) < (m : ℝ) ^ d := pow_pos hm₀ _
    have hc' : (S.card : ℝ) / (m : ℝ) ^ d ≤ T.card := by
      simpa only [T, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hcsize
    exact (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hD
      (pow_le_pow_left₀ hm₀.le hm d)).trans hc'
  · intro a ha b hb j
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have heq := congrArg (fun f : Fin d → Fin m ↦ (f j).val) (ha'.2.trans hb'.2.symm)
    rw [hc a ha'.1 j, hc b hb'.1 j] at heq
    let y := (x a j - l) / h
    let z := (x b j - l) / h
    change ⌊y⌋₊ = ⌊z⌋₊ at heq
    have hy := Nat.floor_le (show 0 ≤ y from div_nonneg (sub_nonneg.mpr (hx a ha'.1 j).1) hh.le)
    have hz := Nat.floor_le (show 0 ≤ z from div_nonneg (sub_nonneg.mpr (hx b hb'.1 j).1) hh.le)
    have hy' := Nat.lt_floor_add_one y
    have hz' := Nat.lt_floor_add_one z
    rw [heq] at hy hy'
    have hdiff : |y - z| ≤ 1 := abs_le.mpr ⟨by linarith only [hy, hz'], by linarith only [hz, hy']⟩
    have he : y - z = (x a j - x b j) / h := by dsimp only [y, z]; ring
    rw [he, abs_div, abs_of_pos hh, div_le_iff₀ hh, one_mul] at hdiff
    exact hdiff

/-- The finite large-cell property for the Lipschitz kernel in Corollary
6.2, with the exact fraction `(h / 2)^d`. -/
theorem exists_large_lipschitz_kernel_cell {α : Type*} [DecidableEq α] {d : ℕ}
    (S : Finset α) (x : α → (Fin d → Icc (0 : ℝ) 1))
    (W : (Fin d → Icc (0 : ℝ) 1) → (Fin d → Icc (0 : ℝ) 1) → Icc (0 : ℝ) 1)
    {h L : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (hsym : ∀ a b, W a b = W b a) (hW : CubeLipschitz L W) :
    ∃ T ⊆ S, (h / 2) ^ d * (S.card : ℝ) ≤ T.card ∧
      ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ e ∈ T, |(W (x a) (x b) : ℝ) - W (x c) (x e)| ≤ 2 * L * h := by
  obtain ⟨T, hTS, hT, hdiam⟩ :=
    exists_large_cube_cell S (fun a j ↦ (x a j : ℝ)) zero_le_one hh
      (fun a _ j ↦ (x a j).property)
  refine ⟨T, hTS, ?_, ?_⟩
  · simp only [sub_zero] at hT
    have hc : (1 : ℝ) / h + 1 ≤ 2 / h := by
      apply (le_div_iff₀ hh).2
      rw [add_mul, div_mul_cancel₀ _ hh.ne', one_mul]
      linarith only [hh₁]
    have hpos : 0 < (1 : ℝ) / h + 1 := by positivity
    have hbound := div_le_div_of_nonneg_left (Nat.cast_nonneg S.card) (pow_pos hpos d)
      (pow_le_pow_left₀ hpos.le hc d)
    calc
      (h / 2) ^ d * (S.card : ℝ) = (S.card : ℝ) / (2 / h) ^ d := by
        rw [div_eq_mul_inv (S.card : ℝ), ← inv_pow, inv_div, mul_comm]
      _ ≤ (T.card : ℝ) := hbound.trans hT
  · intro a ha b hb c hc e he
    have h₁ := hW (x a) (x c) (x b) h hh.le (hdiam a ha c hc)
    have h₂ := hW (x b) (x e) (x c) h hh.le (hdiam b hb e he)
    rw [hsym (x b) (x c), hsym (x e) (x c)] at h₂
    have hz := abs_add_le ((W (x a) (x b) : ℝ) - W (x c) (x b))
      ((W (x c) (x b) : ℝ) - W (x c) (x e))
    rw [sub_add_sub_cancel] at hz
    exact hz.trans (by linarith only [h₁, h₂])

end BoundedEdgeRegularSubgraphs
