module

public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

/-!
# The common degree for the candidate family
-/

public section

namespace BoundedEdgeRegularSubgraphs

/-- An integer within one of the target can be chosen with even total
degree and can be kept in the admissible degree interval. -/
theorem exists_parity_rounded_degree (k : ℕ) (y : ℝ) (hy₀ : 1 ≤ y)
    (hy₁ : y ≤ (k : ℝ) - 2) :
    ∃ d : ℤ, Even ((k : ℤ) * d) ∧ 0 ≤ d ∧ d ≤ (k : ℤ) - 1 ∧ |(d : ℝ) - y| ≤ 1 := by
  have hex : ∃ d : ℤ, Even ((k : ℤ) * d) ∧ |(d : ℝ) - y| ≤ 1 := by
    by_cases hk : Even (k : ℤ)
    · refine ⟨round y, hk.mul_right _, ?_⟩
      rw [abs_sub_comm]
      exact (abs_sub_round y).trans (by norm_num)
    · refine ⟨2 * round (y / 2), ?_, ?_⟩
      · refine ⟨(k : ℤ) * round (y / 2), ?_⟩
        ring
      · push_cast
        rw [show 2 * (round (y / 2) : ℝ) - y = 2 * ((round (y / 2) : ℝ) - y / 2) by ring,
          abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_sub_comm]
        linarith only [abs_sub_round (y / 2)]
  obtain ⟨d, hd, habs⟩ := hex
  obtain ⟨hl, hu⟩ := abs_le.mp habs
  have h₀ : 0 ≤ (d : ℝ) := by linarith only [hl, hy₀]
  have h₁ : (d : ℝ) ≤ (k : ℝ) - 1 := by linarith only [hu, hy₁]
  exact ⟨d, hd, by exact_mod_cast h₀, by exact_mod_cast h₁, habs⟩

end BoundedEdgeRegularSubgraphs
