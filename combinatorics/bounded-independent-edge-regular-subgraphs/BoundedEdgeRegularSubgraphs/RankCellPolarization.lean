module

public import BoundedEdgeRegularSubgraphs.BoundedRowCoordinates
public import BoundedEdgeRegularSubgraphs.CubeCells
import Mathlib.Tactic

/-!
# Diagonal subdivision and polarization for rank cells
-/

public section

open Set Matrix
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

@[expose] noncomputable def rankCellForm {t : ℕ} (B : Matrix (Fin t) (Fin t) ℝ)
    (x y : Fin t → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * B i j * y j

private theorem abs_rankCellForm_le {t : ℕ} (B : Matrix (Fin t) (Fin t) ℝ)
    (hB : ∀ i j, |B i j| ≤ 1) (x y : Fin t → ℝ) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hx : ∀ i, |x i| ≤ C) (hy : ∀ i, |y i| ≤ D) :
    |rankCellForm B x y| ≤ (t : ℝ) ^ 2 * C * D := by
  unfold rankCellForm
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ i : Fin t, ∑ j : Fin t, |x i * B i j * y j| :=
      Finset.sum_le_sum (fun i _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin t, ∑ _j : Fin t, C * D := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul, ← mul_one C]
      exact mul_le_mul (mul_le_mul (hx i) (hB i j) (abs_nonneg _) hC) (hy j) (abs_nonneg _)
        (mul_nonneg hC zero_le_one)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

private theorem rankCellForm_diag_sub {t : ℕ} (B : Matrix (Fin t) (Fin t) ℝ)
    (hB : B.IsSymm) (x y : Fin t → ℝ) :
    rankCellForm B x x - rankCellForm B y y = rankCellForm B (x - y) (x + y) := by
  have hs : rankCellForm B x y = rankCellForm B y x := by
    unfold rankCellForm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show B j i = B i j from congrFun (congrFun hB.eq i) j]
    ring
  have hr : rankCellForm B (x - y) (x + y) =
      rankCellForm B x x - rankCellForm B y y + (rankCellForm B x y - rankCellForm B y x) := by
    simp only [rankCellForm, Pi.sub_apply, Pi.add_apply, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦ by ring))
  rw [hr, hs, sub_self, add_zero]

private theorem rankCellForm_polarization {t : ℕ} (B : Matrix (Fin t) (Fin t) ℝ)
    (hB : B.IsSymm) (x y : Fin t → ℝ) :
    2 * rankCellForm B x y =
      rankCellForm B x x + rankCellForm B y y - rankCellForm B (x - y) (x - y) := by
  have hs : rankCellForm B x y = rankCellForm B y x := by
    unfold rankCellForm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show B j i = B i j from congrFun (congrFun hB.eq i) j]
    ring
  have hr : rankCellForm B (x - y) (x - y) =
      rankCellForm B x x + rankCellForm B y y - (rankCellForm B x y + rankCellForm B y x) := by
    simp only [rankCellForm, Pi.sub_apply, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦ by ring))
  rw [hr, ← hs]
  ring

/-- A small cell of bounded coefficient vectors has a short range of
diagonal values. If a second subdivision controls the diagonal range,
polarization controls all pair entries in that subdivision. -/
theorem rankCell_diagonal_and_polarization {n t : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin t) (Fin t) ℝ)
    (I : Fin n → Fin t → ℝ) (T : Finset (Fin n)) (hB : B.IsSymm)
    (hentry : ∀ i j, |B i j| ≤ 1) (hI : ∀ i j, |I i j| ≤ 1)
    (hA : ∀ i j, A i j = rankCellForm B (I i) (I j))
    {w : ℝ} (hw : 0 ≤ w)
    (hT : ∀ i ∈ T, ∀ j ∈ T, ∀ a, |I i a - I j a| ≤ w) :
    (∀ i ∈ T, ∀ j ∈ T, |A i i - A j j| ≤ 2 * (t : ℝ) ^ 2 * w) ∧
      ∀ U ⊆ T, ∀ h : ℝ, (∀ i ∈ U, ∀ j ∈ U, |A i i - A j j| ≤ h) →
        ∀ i ∈ U, ∀ j ∈ U, ∀ p ∈ U, ∀ q ∈ U, |A i j - A p q| ≤ h + (t : ℝ) ^ 2 * w ^ 2 := by
  constructor
  · intro i hi j hj
    rw [hA i i, hA j j, rankCellForm_diag_sub B hB]
    have hb (a : Fin t) : |(I i + I j) a| ≤ (2 : ℝ) :=
      (abs_add_le _ _).trans (by linarith only [hI i a, hI j a])
    exact (abs_rankCellForm_le B hentry (I i - I j) (I i + I j) hw (by norm_num)
      (hT i hi j hj) hb).trans_eq (by ring)
  · intro U hUT h hdiag i hi j hj p hp q hq
    let b (x y : Fin n) := rankCellForm B (I x - I y) (I x - I y)
    have hp₁ := rankCellForm_polarization B hB (I i) (I j)
    have hp₂ := rankCellForm_polarization B hB (I p) (I q)
    have hp₃ : 2 * (A i j - A p q) =
      (A i i - A p p) + (A j j - A q q) - (b i j - b p q) := by
      rw [hA i j, hA p q, hA i i, hA p p, hA j j, hA q q]
      dsimp only [b]
      linarith only [hp₁, hp₂]
    have hb (x y : Fin n) (hx : x ∈ U) (hy : y ∈ U) :
        |b x y| ≤ (t : ℝ) ^ 2 * w ^ 2 := by
      exact (abs_rankCellForm_le B hentry (I x - I y) (I x - I y) hw hw
        (hT x (hUT hx) y (hUT hy)) (hT x (hUT hx) y (hUT hy))).trans_eq (by ring)
    have hdiff (x y : ℝ) : |x - y| ≤ |x| + |y| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)
    have hpol := hdiff ((A i i - A p p) + (A j j - A q q)) (b i j - b p q)
    rw [← hp₃, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hpol
    linarith only [hpol, abs_add_le (A i i - A p p) (A j j - A q q),
      hdiff (b i j) (b p q), hdiag i hi p hp, hdiag j hj q hq, hb i j hi hj, hb p q hp hq]

end BoundedEdgeRegularSubgraphs
