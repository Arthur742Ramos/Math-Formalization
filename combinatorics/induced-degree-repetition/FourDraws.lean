module

public import FourthMoment
public import UniformMean
public import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

public section
namespace InducedDegreeRepetition.Sampling

open Finset
open scoped Classical
variable {I X : Type*}

@[expose] def quadEquiv (α : Type*) : (Fin 4 → α) ≃ α × α × α × α where
  toFun z := (z 0,z 1,z 2,z 3)
  invFun p := ![p.1,p.2.1,p.2.2.1,p.2.2.2]
  left_inv z := funext fun j => by fin_cases j <;> rfl
  right_inv p := rfl

@[expose] def rectangleTerm (A : X → X → ℝ) (z : Fin 4 → X) :=
  (A (z 2) (z 0)*A (z 2) (z 1))*(A (z 3) (z 0)*A (z 3) (z 1))

theorem four_sum [Fintype X] (A : X → X → ℝ) :
    (∑ z : Fin 4 → X, rectangleTerm A z) = fourthMoment A univ := by
  have h := Fintype.sum_equiv (quadEquiv X) (rectangleTerm A)
    (fun p => (A p.2.2.1 p.1*A p.2.2.1 p.2.1)*(A p.2.2.2 p.1*A p.2.2.2 p.2.1)) (fun _ => rfl)
  rw [h]
  simp only [Fintype.sum_prod_type,fourthMoment,gram,pow_two,sum_mul,mul_sum]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  rw [sum_comm]

/-- The upper bound counts repeated indices, even when two independently drawn
vertex labels happen to coincide. -/
theorem repeated_quadruples [Fintype I] [DecidableEq I] :
    (univ.filter (fun z : Fin 4 → I => ¬Function.Injective z)).card ≤ 6*(Fintype.card I)^3 := by
  classical
  let h := Fintype.card I
  have inj : (univ.filter (fun z : Fin 4 → I => Function.Injective z)).card = h.descFactorial 4 := by
    rw [← Fintype.card_coe]
    let e : {z // z ∈ univ.filter (fun z : Fin 4 → I => Function.Injective z)} ≃ (Fin 4 ↪ I) :=
      ⟨fun z => ⟨z.val,(mem_filter.mp z.2).2⟩,fun i => ⟨i,mem_filter.mpr ⟨mem_univ _,i.injective⟩⟩,
       fun _ => rfl,fun _ => rfl⟩
    rw [Fintype.card_congr e,Fintype.card_embedding_eq,Fintype.card_fin]
  have all := card_filter_add_card_filter_not (s:=(univ:Finset (Fin 4 → I))) Function.Injective
  rw [inj,card_univ,Fintype.card_fun,Fintype.card_fin] at all
  have cap : h^4 ≤ h.descFactorial 4+6*h^3 := by
    rcases h with _|_|_|h
    all_goals simp only [Nat.descFactorial_succ,Nat.descFactorial_zero,Nat.succ_sub_succ_eq_sub,Nat.sub_zero,Nat.sub_self]
    all_goals simp <;> try nlinarith [Nat.zero_le (h^2)]
  dsimp [h] at cap all
  omega

end InducedDegreeRepetition.Sampling
