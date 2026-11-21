module

public import MeanMarginals
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

public section
namespace InducedDegreeRepetition.Sampling

open Finset
open scoped Classical
variable {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I]

theorem union_indicator (p : I → Prop) : indicator (∃ i, p i) ≤ ∑ i, indicator (p i) := by
  classical
  by_cases h : ∃ i, p i
  · obtain ⟨i,hi⟩ := h
    rw [show indicator (∃ i, p i) = indicator (p i) by simp [indicator,hi,show ∃ i, p i from ⟨i,hi⟩]]
    exact single_le_sum (fun _ _ => indicator_nonneg _) (mem_univ i)
  · simp only [indicator,ite_eq_right h]
    apply sum_nonneg
    intro _ _
    split <;> norm_num

omit [Nonempty Ω] in
theorem mean_union (p : I → Ω → Prop) (δ : ℝ)
    (h : ∀ i, mean (fun ω => indicator (p i ω)) ≤ δ) :
    mean (fun ω => indicator (∃ i, p i ω)) ≤ Fintype.card I*δ := by
  apply (mean_le _ _ (fun ω => union_indicator (fun i => p i ω))).trans
  rw [mean_sum]
  exact (sum_le_sum (s:=univ) (fun i _ => h i)).trans_eq (by simp)

theorem choose_four (p q s t : Ω → Prop)
    (hp : mean (fun x => indicator (p x)) ≤ 1/8)
    (hq : mean (fun x => indicator (q x)) ≤ 1/8)
    (hs : mean (fun x => indicator (s x)) ≤ 1/8)
    (ht : mean (fun x => indicator (t x)) ≤ 1/8) :
    ∃ x, ¬p x ∧ ¬q x ∧ ¬s x ∧ ¬t x := by
  classical
  by_contra! h
  have point (x : Ω) : 1 ≤ indicator (p x)+indicator (q x)+indicator (s x)+indicator (t x) := by
    by_cases a : p x <;> by_cases b : q x <;> by_cases c : s x <;> by_cases d : t x <;> simp_all [indicator]
    all_goals norm_num
  have m := mean_le _ _ point
  simp only [mean_const,mean_add] at m
  linarith

end InducedDegreeRepetition.Sampling
