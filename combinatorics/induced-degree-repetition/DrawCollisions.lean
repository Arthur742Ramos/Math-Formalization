module

public import UniformMean
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Sampling

open Finset
open scoped Classical
variable {I X : Type*} [Fintype I] [Fintype X] [DecidableEq I] [Nonempty X]

theorem mean_pair (i j : I) (ne : i ≠ j) (f : X → X → ℝ) :
    mean (fun ys : I → X => f (ys i) (ys j)) = mean (fun x => mean (f x)) := by
  classical
  let g : Fin 2 ↪ I := ⟨![i,j],by
    intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩
  let ev (z : Fin 2 → X) := f (z 0) (z 1)
  have h := mean_restrict (X:=X) g ev
  change mean (fun ys : I → X => ev (fun k => ys (g k))) = _
  rw [h]
  have eq := mean_equiv (finTwoArrowEquiv X) ev (fun p => f p.1 p.2) (fun _ => rfl)
  rw [eq,mean_prod]

theorem collision_mean : mean (fun ys : I → X => if ¬Function.Injective ys then (1:ℝ) else 0) ≤
    (Fintype.card I:ℝ)^2/Fintype.card X := by
  classical
  let term (i j : I) (ys : I → X) := if i ≠ j ∧ ys i=ys j then (1:ℝ) else 0
  have per (i j : I) : mean (term i j) ≤ 1/Fintype.card X := by
    by_cases h : i=j
    · subst j
      simp [term,mean]
    · have pair := mean_pair i j h (fun x z : X => if x=z then (1:ℝ) else 0)
      have one (x : X) : mean (fun z : X => if x=z then (1:ℝ) else 0) = 1/Fintype.card X := by
        simp [mean]
      simp only [one,mean_const] at pair
      simpa [term,h] using pair.le
  have counts (ys : I → X) : (if ¬Function.Injective ys then (1:ℝ) else 0) ≤
      ∑ i, ∑ j, term i j ys := by
    by_cases h : Function.Injective ys
    · simp only [ite_eq_right (not_not.mpr h)]
      exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => by dsimp [term]; split <;> norm_num
    · obtain ⟨i,j,same,diff⟩ := Function.not_injective_iff.mp h
      rw [ite_eq_left h]
      have one : term i j ys = 1 := by simp [term,same,diff]
      rw [← one]
      apply (single_le_sum (f:=fun j => term i j ys) (fun _ _ => by dsimp [term]; split <;> norm_num) (mem_univ j)).trans
      exact single_le_sum (f:=fun i => ∑ j, term i j ys) (fun _ _ => sum_nonneg fun _ _ => by dsimp [term]; split <;> norm_num) (mem_univ i)
  apply (mean_le _ _ counts).trans
  rw [mean_sum]
  simp_rw [mean_sum]
  apply (sum_le_sum (s:=univ) fun i _ => sum_le_sum (s:=univ) fun j _ => per i j).trans_eq
  simp
  ring

end InducedDegreeRepetition.Sampling
