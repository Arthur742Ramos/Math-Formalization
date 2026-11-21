module

public import FourDraws
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Sampling

open Finset
open scoped Classical
variable {I X : Type*} [Fintype I] [Fintype X] [DecidableEq I] [Nonempty X]

/-- Fourth moment of the centered matrix induced by an ordered sample with
replacement. The exceptional term comes only from repeated sample positions. -/
theorem sampled_fourth (A : X → X → ℝ) (unit : ∀ x y, |A x y| ≤ 1) :
    mean (fun ys : I → X => fourthMoment (fun i j => A (ys i) (ys j)) univ) ≤
      (Fintype.card I:ℝ)^4*(fourthMoment A univ/(Fintype.card X:ℝ)^4) + 6*(Fintype.card I:ℝ)^3 := by
  classical
  let v := fourthMoment A univ/(Fintype.card X:ℝ)^4
  have vp : 0 ≤ v := by dsimp [v,fourthMoment]; positivity
  have ave : mean (rectangleTerm A) = v := by rw [mean,four_sum]; simp [v]
  have bound (z : Fin 4 → I) : mean (fun ys : I → X => rectangleTerm A (fun k => ys (z k))) ≤
      v + (if ¬Function.Injective z then 1 else 0) := by
    by_cases distinct : Function.Injective z
    · rw [ite_eq_right (not_not.mpr distinct),add_zero,← ave]
      apply le_of_eq
      convert mean_restrict (X:=X) (⟨z,distinct⟩ : Fin 4 ↪ I) (rectangleTerm A) using 1
    · have h : mean (fun ys : I → X => rectangleTerm A (fun k => ys (z k))) ≤ 1 := by
        rw [← mean_const (X:=I → X) 1]
        apply mean_le
        intro ys
        apply (le_abs_self _).trans
        simp only [rectangleTerm,abs_mul]
        calc
          _ ≤ ((1:ℝ)*1)*(1*1) := by
            apply mul_le_mul _ _ (by positivity) (by norm_num)
            all_goals exact mul_le_mul (unit ..) (unit ..) (abs_nonneg _) zero_le_one
          _ = _ := by norm_num
      simp [distinct]
      linarith
  have swap : mean (fun ys : I → X => fourthMoment (fun i j => A (ys i) (ys j)) univ) =
      ∑ z : Fin 4 → I, mean (fun ys : I → X => rectangleTerm A (fun k => ys (z k))) := by
    simp_rw [← four_sum]
    exact mean_sum _ _
  rw [swap]
  apply (sum_le_sum (s:=univ) fun z _ => bound z).trans
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,sum_boole]
  have cap : (((univ.filter (fun z : Fin 4 → I => ¬Function.Injective z)).card:ℝ)) ≤ 6*(Fintype.card I:ℝ)^3 := by
    exact_mod_cast repeated_quadruples (I:=I)
  exact add_le_add_right cap _

end InducedDegreeRepetition.Sampling
