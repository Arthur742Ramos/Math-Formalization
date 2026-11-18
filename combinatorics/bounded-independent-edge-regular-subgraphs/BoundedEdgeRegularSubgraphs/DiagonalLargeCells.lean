module

public import BoundedEdgeRegularSubgraphs.StructuralLargeCells
import Mathlib.Tactic

/-!
# Improved Lipschitz cells from a quadratic diagonal difference
-/

public section

open Set

namespace BoundedEdgeRegularSubgraphs

/-- The additional condition in Remark 6.5 in the maximum norm. -/
@[expose] def CubeDiagonalQuadratic {d : ℕ} (B : ℝ)
    (W : (Fin d → Icc (0 : ℝ) 1) → (Fin d → Icc (0 : ℝ) 1) → Icc (0 : ℝ) 1) : Prop :=
  ∀ x y ε, 0 ≤ ε → (∀ i, |(x i : ℝ) - y i| ≤ ε) →
    |(W x x : ℝ) + (W y y : ℝ) - 2 * (W x y : ℝ)| ≤ B * ε ^ 2

/-- Refining a spatial cell by the diagonal values gives the finite
large-cell hypothesis of Remark 6.5. -/
theorem hasLargeBalancedCells_of_diagonal_quadratic {n d : ℕ} {L B : ℝ}
    (hL : 0 ≤ L) (hB : 0 ≤ B)
    (x : Fin n → (Fin d → Icc (0 : ℝ) 1))
    (W : (Fin d → Icc (0 : ℝ) 1) → (Fin d → Icc (0 : ℝ) 1) → Icc (0 : ℝ) 1)
    (hSymm : ∀ a b, W a b = W b a) (hW : CubeLipschitz L W) (hD : CubeDiagonalQuadratic B W) :
    HasLargeBalancedCells (((d : ℝ) + 1) / 2) (((2 : ℝ) ^ d * (4 * L + 1))⁻¹)
      (1 + B) (fun e ↦ W (x e.val.1) (x e.val.2)) := by
  classical
  intro S h hh hh₁ hSize
  let v := Real.sqrt h
  have hv : 0 < v := Real.sqrt_pos.mpr hh
  have hv₁ : v ≤ 1 := Real.sqrt_le_iff.mpr ⟨by norm_num, by simpa only [one_pow] using hh₁⟩
  have hv₂ : v ^ 2 = h := Real.sq_sqrt hh.le
  obtain ⟨T, hTS, hT, hDiam⟩ :=
    exists_large_cube_cell S (fun a j ↦ (x a j : ℝ)) zero_le_one hv (fun a _ j ↦ (x a j).property)
  have hS : 0 < S.card := by
    by_contra! hn
    have hZ : S.card = 0 := by omega
    simp [hZ] at hSize
    norm_num at hSize
  have hT₀ : 0 < T.card := by
    have h : 0 < (T.card : ℝ) :=
      (div_pos (Nat.cast_pos.mpr hS) (pow_pos (by linarith only [div_pos zero_lt_one hv]) d)).trans_le hT
    exact_mod_cast h
  obtain ⟨a₀, ha₀⟩ := Finset.card_pos.mp hT₀
  let D (i : Fin n) := (W (x i) (x i) : ℝ)
  let c := D a₀
  have hDiag (i : Fin n) (hi : i ∈ T) : D i ∈ Icc (c - 2 * L * v) (c + 2 * L * v) := by
    have h₁ := hW (x i) (x a₀) (x i) v hv.le (hDiam i hi a₀ ha₀)
    have h₂ := hW (x i) (x a₀) (x a₀) v hv.le (hDiam i hi a₀ ha₀)
    rw [hSymm (x a₀) (x i)] at h₁
    have h := (abs_sub_le (D i) (W (x i) (x a₀) : ℝ) c).trans (add_le_add h₁ h₂)
    rcases abs_le.mp h with ⟨h₁', h₂'⟩
    exact ⟨by linarith only [h₁'], by linarith only [h₂']⟩
  obtain ⟨U, hUT, hU, hUD⟩ := exists_large_cube_cell (d := 1) T
    (fun i _ ↦ D i) (by nlinarith only [mul_nonneg hL hv.le] :
      c - 2 * L * v ≤ c + 2 * L * v) hh (fun i hi _ ↦ hDiag i hi)
  have hT' : (v / 2) ^ d * (S.card : ℝ) ≤ (T.card : ℝ) := by
    simp only [sub_zero] at hT
    have hc : 1 / v + 1 ≤ 2 / v := by
      apply (le_div_iff₀ hv).2
      rw [add_mul, div_mul_cancel₀ _ hv.ne', one_mul]
      linarith only [hv₁]
    have hb := div_le_div_of_nonneg_left (Nat.cast_nonneg S.card) (pow_pos (by positivity) d)
      (pow_le_pow_left₀ (by positivity) hc d)
    rw [div_eq_mul_inv (S.card : ℝ), ← inv_pow, inv_div, mul_comm] at hb
    exact hb.trans hT
  have hU' : (v / (4 * L + 1)) * (T.card : ℝ) ≤ U.card := by
    have hDen : (c + 2 * L * v - (c - 2 * L * v)) / h + 1 = (4 * L + v) / v := by
      rw [← hv₂]
      field_simp [hv.ne']
      <;> ring
    rw [hDen, pow_one] at hU
    have hden : 0 < (4 * L + v) / v := by positivity
    have hdom : (4 * L + v) / v ≤ (4 * L + 1) / v :=
      div_le_div_of_nonneg_right (add_le_add_right hv₁ _) hv.le
    have h := (div_le_div_of_nonneg_left (Nat.cast_nonneg T.card) hden hdom).trans hU
    rw [div_div_eq_mul_div, mul_comm] at h
    simpa only [div_mul_eq_mul_div] using h
  have hCard := (mul_le_mul_of_nonneg_left hT' (show 0 ≤ v / (4 * L + 1) by positivity)).trans hU'
  have hRpow : v ^ (d + 1) = h ^ (((d : ℝ) + 1) / 2) := by
    dsimp only [v]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hh.le]
    push_cast
    congr 1
    ring
  have hCount : (((2 : ℝ) ^ d * (4 * L + 1))⁻¹) * (S.card : ℝ) *
      h ^ (((d : ℝ) + 1) / 2) ≤ (U.card : ℝ) := by
    rw [← hRpow]
    convert hCard using 1
    rw [pow_succ, div_pow]
    field_simp
  refine ⟨U, hUT.trans hTS, hCount, ?_⟩
  have hU₂ : 2 ≤ Fintype.card U := by
    rw [Fintype.card_coe]
    exact_mod_cast hSize.trans hCount
  let q : Edge (Fin n) → Icc (0 : ℝ) 1 := fun e ↦ W (x e.val.1) (x e.val.2)
  have hPairs (a b : Fin n) (ha : a ∈ U) (hb : b ∈ U) :
      |D a + D b - 2 * (W (x a) (x b) : ℝ)| ≤ B * h := by
    rw [← hv₂]
    exact hD _ _ v hv.le (hDiam a (hUT ha) b (hUT hb))
  have hRange (e f : Edge U) : |(induce U q e).val - (induce U q f).val| ≤ (1 + B) * h := by
    rcases e with ⟨⟨a, b⟩, he⟩
    rcases f with ⟨⟨g, j⟩, hf⟩
    have h₁ := abs_le.mp (hPairs a.val b.val a.property b.property)
    have h₂ := abs_le.mp (hPairs g.val j.val g.property j.property)
    have h₃ := abs_le.mp (hUD a.val a.property g.val g.property (0 : Fin 1))
    have h₄ := abs_le.mp (hUD b.val b.property j.val j.property (0 : Fin 1))
    change |(W (x a.val) (x b.val) : ℝ) - (W (x g.val) (x j.val) : ℝ)| ≤ _
    exact abs_le.mpr ⟨by nlinarith only [h₁.2, h₂.1, h₃.1, h₄.1],
      by nlinarith only [h₁.1, h₂.2, h₃.2, h₄.2]⟩
  simpa only [Fintype.card_coe] using normalized_degree_sub_density_le_of_range (induce U q) hU₂ hRange

end BoundedEdgeRegularSubgraphs
