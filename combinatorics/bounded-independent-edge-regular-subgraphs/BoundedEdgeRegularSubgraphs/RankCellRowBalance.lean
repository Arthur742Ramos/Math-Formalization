module

public import BoundedEdgeRegularSubgraphs.RankCells
public import BoundedEdgeRegularSubgraphs.CellRowBalance
import BoundedEdgeRegularSubgraphs.Induce
import Mathlib.Tactic

/-!
# Near-balance from a bounded rank completion
-/

public section

open Set Matrix
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- If all edge probabilities differ by at most b, every normalized
degree differs from the density by at most b. -/
theorem normalized_degree_sub_density_le_of_range {α : Type*} [Fintype α] [LinearOrder α]
    (q : Edge α → Icc (0 : ℝ) 1) (hn : 2 ≤ Fintype.card α) {b : ℝ}
    (hRange : ∀ e f, |(q e : ℝ) - q f| ≤ b) :
    ∀ i, |degreeSum (fun e ↦ (q e : ℝ)) i / ((Fintype.card α : ℝ) - 1) - arrayDensity q| ≤ b := by
  classical
  have hn' : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  have hE : (Finset.univ : Finset (Edge α)).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_univ]
    have h := mul_pos (show (0 : ℝ) < Fintype.card α by linarith only [hn'])
      (show 0 < (Fintype.card α : ℝ) - 1 by linarith only [hn'])
    rw [← card_edge_twice] at h
    exact_mod_cast (show (0 : ℝ) < Fintype.card (Edge α) by linarith only [h])
  obtain ⟨f, _, hf⟩ := Finset.exists_min_image Finset.univ (fun e ↦ (q e : ℝ)) hE
  have hb (e : Edge α) : (q e : ℝ) ≤ (q f : ℝ) + b := by
    linarith only [(le_abs_self ((q e : ℝ) - q f)).trans (hRange e f)]
  have h := row_density_mem_Icc q hn (fun e ↦ hf e (Finset.mem_univ _)) hb
  intro i
  exact abs_le.mpr ⟨by linarith only [(h.2 i).1, h.1.2], by linarith only [(h.2 i).2, h.1.1]⟩

/-- The finite hypothesis (6.1) for Corollary 6.4, with the manuscript's
constants and the exponent (r + 1) / 2. -/
theorem exists_lowRank_nearBalanced_cell {n r : ℕ} (p : Edge (Fin n) → Icc (0 : ℝ) 1)
    (hp : HasRankCompletion r p) (S : Finset (Fin n)) {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (hsize : 2 ≤ (S.card : ℝ) * (h ^ (((r : ℝ) + 1) / 2) / (3 ^ r * (2 * (r : ℝ) ^ 2 + 1)))) :
    ∃ T ⊆ S, (S.card : ℝ) * (h ^ (((r : ℝ) + 1) / 2) / (3 ^ r * (2 * (r : ℝ) ^ 2 + 1))) ≤ T.card ∧
      ∀ i : T, |degreeSum (fun e ↦ (induce T p e).val) i / ((T.card : ℝ) - 1) -
          arrayDensity (induce T p)| ≤ (1 + (r : ℝ) ^ 2) * h := by
  obtain ⟨A, hA, hB, hRank, hP⟩ := hp
  have hSymm : A.IsSymm := by
    ext i j
    exact hA j i
  obtain ⟨T, hTS, hT, hDiam⟩ := exists_large_lowRank_cell A hSymm hRank hB S hh hh₁
  have hrpow : (Real.sqrt h) ^ (r + 1) = h ^ (((r : ℝ) + 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hh.le]
    congr 1
    push_cast
    ring
  rw [hrpow] at hT
  refine ⟨T, hTS, hT, ?_⟩
  have hcard : 2 ≤ Fintype.card T := by
    rw [Fintype.card_coe]
    exact_mod_cast hsize.trans hT
  have h := normalized_degree_sub_density_le_of_range (induce T p) hcard
    (fun e f ↦ by
      have hd := hDiam e.val.1.val e.val.1.property e.val.2.val e.val.2.property
        f.val.1.val f.val.1.property f.val.2.val f.val.2.property
      change |A (inducedEdge T e).val.1 (inducedEdge T e).val.2 -
        A (inducedEdge T f).val.1 (inducedEdge T f).val.2| ≤ _ at hd
      rw [hP (inducedEdge T e), hP (inducedEdge T f)] at hd
      exact hd)
  simpa only [Fintype.card_coe] using h

end BoundedEdgeRegularSubgraphs
