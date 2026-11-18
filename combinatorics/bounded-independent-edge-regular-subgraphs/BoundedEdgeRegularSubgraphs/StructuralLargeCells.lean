module

public import BoundedEdgeRegularSubgraphs.LargeCellAmplification
public import BoundedEdgeRegularSubgraphs.RankCellRowBalance
import Mathlib.Tactic

/-!
# Large-cell hypotheses for the structural models
-/

public section

open Set

namespace BoundedEdgeRegularSubgraphs

theorem hasLargeBalancedCells_of_lipschitz {n d : ℕ} {L : ℝ}
    (x : Fin n → (Fin d → Icc (0 : ℝ) 1))
    (W : (Fin d → Icc (0 : ℝ) 1) → (Fin d → Icc (0 : ℝ) 1) → Icc (0 : ℝ) 1)
    (hSymm : ∀ a b, W a b = W b a) (hW : CubeLipschitz L W) :
    HasLargeBalancedCells (d : ℝ) ((2 : ℝ) ^ d)⁻¹ (2 * L)
      (fun e ↦ W (x e.val.1) (x e.val.2)) := by
  intro S h hh hh₁ hS
  have hc : (((2 : ℝ) ^ d)⁻¹) * (S.card : ℝ) * h ^ (d : ℝ) =
      (h / 2) ^ d * (S.card : ℝ) := by
    rw [Real.rpow_natCast, div_pow, div_eq_mul_inv]
    ring
  rw [hc] at hS ⊢
  obtain ⟨T, hT₀, hT₁, hT₂⟩ := exists_lipschitz_nearBalanced_cell S x W hh hh₁ hSymm hW hS
  exact ⟨T, hT₀, hT₁, hT₂⟩

theorem hasLargeBalancedCells_of_rank {n r : ℕ} (p : Edge (Fin n) → Icc (0 : ℝ) 1)
    (hp : HasRankCompletion r p) :
    HasLargeBalancedCells (((r : ℝ) + 1) / 2) ((3 ^ r * (2 * (r : ℝ) ^ 2 + 1))⁻¹)
      (1 + (r : ℝ) ^ 2) p := by
  intro S h hh hh₁ hS
  have hc : ((3 ^ r * (2 * (r : ℝ) ^ 2 + 1))⁻¹) * (S.card : ℝ) * h ^ (((r : ℝ) + 1) / 2) =
      (S.card : ℝ) * (h ^ (((r : ℝ) + 1) / 2) / (3 ^ r * (2 * (r : ℝ) ^ 2 + 1))) := by
    rw [div_eq_mul_inv]
    ring
  rw [hc] at hS ⊢
  exact exists_lowRank_nearBalanced_cell p hp S hh hh₁ hS

end BoundedEdgeRegularSubgraphs
