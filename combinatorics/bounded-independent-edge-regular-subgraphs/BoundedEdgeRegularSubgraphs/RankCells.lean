module

public import BoundedEdgeRegularSubgraphs.RankCellPolarization
import Mathlib.Tactic

/-!
# Lemma 6.3: large low-rank cells
-/

public section

open Set Matrix
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- In any principal submatrix of a bounded symmetric rank-r matrix,
the induced entries have range at most (1 + r²) times the resolution
on a cell with the fraction stated in Lemma 6.3. -/
theorem exists_large_lowRank_cell {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hArank : A.rank ≤ r) (hBound : ∀ i j, A i j ∈ Icc (0 : ℝ) 1)
    (S : Finset (Fin n)) {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) :
    ∃ U ⊆ S, (S.card : ℝ) * ((Real.sqrt h) ^ (r + 1) / (3 ^ r * (2 * (r : ℝ) ^ 2 + 1))) ≤
      (U.card : ℝ) ∧
      ∀ i ∈ U, ∀ j ∈ U, ∀ p ∈ U, ∀ q ∈ U, |A i j - A p q| ≤ (1 + (r : ℝ) ^ 2) * h := by
  classical
  let t := A.rank
  let w := Real.sqrt h
  have hw : 0 < w := Real.sqrt_pos.mpr hh
  have hw₁ : w ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hh₁
  have hsq : w ^ 2 = h := Real.sq_sqrt hh.le
  obtain ⟨I, x, hx, hI⟩ := exists_bounded_matrix_symmetric_coordinates A hA
  let B := A.submatrix I I
  have hB : B.IsSymm := by
    ext i j
    exact congrFun (congrFun hA.eq (I i)) (I j)
  have hB₀ (i j : Fin t) : |B i j| ≤ 1 := by
    change |A (I i) (I j)| ≤ 1
    rw [abs_of_nonneg (hBound _ _).1]
    exact (hBound _ _).2
  obtain ⟨T, hTS, hTc, hTx⟩ := exists_large_cube_cell S x
    (show (-1 : ℝ) ≤ 1 by norm_num) hw (fun i _ j ↦ abs_le.mp (hx i j))
  have hsize₁ : (S.card : ℝ) / (3 / w) ^ r ≤ (T.card : ℝ) := by
    have h₁ : (1 - (-1) : ℝ) / w + 1 ≤ (3 : ℝ) / w := by
      apply (le_div_iff₀ hw).2
      rw [add_mul, div_mul_cancel₀ _ hw.ne', one_mul]
      linarith only [hw₁]
    have hp : (0 : ℝ) < (1 - (-1)) / w + 1 := by positivity
    have hb : 1 ≤ (3 : ℝ) / w := (le_div_iff₀ hw).2 (by linarith only [hw₁])
    have h₂ := (pow_le_pow_left₀ hp.le h₁ t).trans (pow_le_pow_right₀ hb hArank)
    exact (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos hp _) h₂).trans hTc
  let K := 2 * (r : ℝ) ^ 2 + 1
  by_cases hT : T.Nonempty
  · obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image T (fun i ↦ A i i) hT
    have hrep (i j : Fin n) : A i j = rankCellForm B (x i) (x j) := hI i j
    obtain ⟨hDi, hPo⟩ := rankCell_diagonal_and_polarization A B x T hB hB₀ hx hrep hw.le hTx
    let D := 2 * (t : ℝ) ^ 2 * w
    have hD : 0 ≤ D := by dsimp only [D]; positivity
    have hdiag (i : Fin n) (hi : i ∈ T) : A i i ∈ Icc (A i₀ i₀) (A i₀ i₀ + D) := by
      exact ⟨hmin i hi, by linarith only [(abs_le.mp (hDi i hi i₀ hi₀)).2]⟩
    obtain ⟨U, hUT, hUc, hUx⟩ := exists_large_cube_cell T
      (fun i (_ : Fin 1) ↦ A i i) (show A i₀ i₀ ≤ A i₀ i₀ + D by linarith only [hD])
      hh (fun i hi _ ↦ hdiag i hi)
    have ht : (t : ℝ) ≤ r := by exact_mod_cast hArank
    have ht₂ : (t : ℝ) ^ 2 ≤ (r : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) ht 2
    have hsize₂ : (T.card : ℝ) / (K / w) ≤ (U.card : ℝ) := by
      have hg : (A i₀ i₀ + D - A i₀ i₀) / h + 1 ≤ K / w := by
        rw [add_sub_cancel_left, (show D / h = 2 * (t : ℝ) ^ 2 / w by
          dsimp only [D]
          rw [← hsq]
          field_simp [hw.ne']
          <;> ring)]
        apply (le_div_iff₀ hw).2
        rw [add_mul, div_mul_cancel₀ _ hw.ne', one_mul]
        dsimp only [K]
        linarith only [ht₂, hw₁]
      have hd : 0 < (A i₀ i₀ + D - A i₀ i₀) / h + 1 := by rw [add_sub_cancel_left]; positivity
      rw [pow_one] at hUc
      exact (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd hg).trans hUc
    refine ⟨U, hUT.trans hTS, ?_, ?_⟩
    · have he : (S.card : ℝ) * (w ^ (r + 1) / (3 ^ r * K)) =
          ((S.card : ℝ) / (3 / w) ^ r) / (K / w) := by
        rw [div_div, div_pow, div_mul_div_comm, ← pow_succ, div_div_eq_mul_div, mul_div_assoc]
      change (S.card : ℝ) * (w ^ (r + 1) / (3 ^ r * K)) ≤ _
      rw [he]
      exact (div_le_div_of_nonneg_right hsize₁ (by dsimp only [K]; positivity)).trans hsize₂
    · intro i hi j hj p hp q hq
      have hb := hPo U hUT h (fun i hi j hj ↦ hUx i hi j hj (0 : Fin 1)) i hi j hj p hp q hq
      rw [hsq] at hb
      exact hb.trans (by nlinarith only [mul_le_mul_of_nonneg_right ht₂ hh.le])
  · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    rw [hTempty, Finset.card_empty, Nat.cast_zero] at hsize₁
    have hzero : (S.card : ℝ) = 0 := by
      have hh := (div_le_iff₀ (show 0 < (3 / w) ^ r by positivity)).mp hsize₁
      exact le_antisymm (by simpa only [zero_mul] using hh) (Nat.cast_nonneg _)
    exact ⟨∅, Finset.empty_subset _, by rw [hzero, zero_mul, Finset.card_empty, Nat.cast_zero],
      fun _ hi ↦ False.elim (Finset.notMem_empty _ hi)⟩

end BoundedEdgeRegularSubgraphs
