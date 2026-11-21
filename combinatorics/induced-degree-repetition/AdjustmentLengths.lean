module

public import DyadicRates
public import IntegerTotals
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Edit

open Filter Finset
open scoped Topology Classical

/-- The mass budget accommodates the registered exterior profile and the edits. -/
@[expose] noncomputable def budget (L : ℕ) := 4*Real.log ((L:ℝ)+1)+2

theorem budget_pos (L : ℕ) : 0 < budget L := by
  have := Real.log_nonneg (show 1 ≤ (L:ℝ)+1 by linarith [Nat.cast_nonneg (α := ℝ) L])
  dsimp [budget]; linarith

theorem dyadic_budget (k : ℝ) (hk : 0 < k) :
    ∀ᶠ j : ℕ in atTop, budget (2^j) ≤ k*(2:ℝ)^j := by
  have rate := (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<2)).eventually_lt_const
    (show 0 < k/10 by positivity)
  filter_upwards [rate,eventually_ge_atTop 1] with j hj hj1
  simp only [pow_one] at hj
  have bound := (div_lt_iff₀ (by positivity : (0:ℝ)<2^j)).mp hj
  have up := Real.log_le_log (show (0:ℝ) < 2^j+1 by positivity)
    (show (2:ℝ)^j+1 ≤ 2^(j+1) by rw [pow_succ]; linarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=j)])
  rw [Real.log_pow] at up
  have log2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  dsimp [budget]
  push_cast at *
  nlinarith [mul_le_mul_of_nonneg_left log2 (show (0:ℝ) ≤ (j:ℝ)+1 by positivity),
    (show (1:ℝ)≤j by exact_mod_cast hj1)]

theorem choose_lengths (k : ℝ) (hk : 0 < k) (b : ℕ → ℕ → ℝ)
    (limits : ∀ q, 3 ≤ q → Tendsto (fun j : ℕ => b q (2^j)/Real.log ((2:ℝ)^j+1)) atTop atTop) :
    ∃ j₀ j₁ : ℕ, 2 ≤ j₀ ∧ j₀ < j₁ ∧ budget (2^j₀) ≤ k*(2:ℝ)^j₀ ∧
      budget (2^j₁) ≤ k*(2:ℝ)^j₁ ∧ ∀ q, TestModulus (2^j₀) q → budget (2^j₁) < b q (2^j₁) := by
  obtain ⟨j₀,h₀,s₀⟩ := ((eventually_ge_atTop 2).and (dyadic_budget k hk)).exists
  let mods := (range (max 4 (2^j₀)+1)).filter (TestModulus (2^j₀))
  have mem (q) (h : TestModulus (2^j₀) q) : q ∈ mods := by
    apply mem_filter.mpr
    refine ⟨mem_range.mpr ?_,h⟩
    rcases h with h|h <;> omega
  have all : ∀ᶠ j : ℕ in atTop, ∀ q ∈ mods, budget (2^j) < b q (2^j) := by
    apply (eventually_all_finset mods).mpr
    intro q hq
    have hm := (mem_filter.mp hq).2
    have qp : 3 ≤ q := by rcases hm with hm|hm <;> omega
    have log2 := Real.log_pos (by norm_num : (1:ℝ)<2)
    have lim := (limits q qp).eventually_gt_atTop (4+2/Real.log 2)
    filter_upwards [lim] with j hj
    have ge := Real.log_le_log (by norm_num : (0:ℝ)<2)
      (show (2:ℝ)≤2^j+1 by linarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=j)])
    have bound := (lt_div_iff₀ (log2.trans_le ge)).mp hj
    have prod := mul_le_mul_of_nonneg_left ge (show 0 ≤ 2/Real.log 2 by positivity)
    rw [div_mul_cancel₀ _ log2.ne'] at prod
    dsimp [budget]
    push_cast
    linarith
  obtain ⟨j₁,h₁,s₁,hm⟩ := ((eventually_gt_atTop j₀).and ((dyadic_budget k hk).and all)).exists
  exact ⟨j₀,j₁,h₀,h₁,s₀,s₁,fun q h => hm q (mem q h)⟩

end InducedDegreeRepetition.Edit
