module

public import ProfileSampling
public import RestrictedAtoms
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

public section
namespace InducedDegreeRepetition.Edit

open Finset
open scoped Classical
variable {I X Y : Type*} [Fintype I] [DecidableEq I]

theorem coordinate_bad (pool : I → Finset X) (i : I) (p : X → Prop) (ε : ℝ)
    (h : (((pool i).filter p).card:ℝ) ≤ ε*(pool i).card) :
    (((Fintype.piFinset pool).filter fun x => p (x i)).card:ℝ) ≤ ε*(Fintype.piFinset pool).card := by
  classical
  let pool' := Function.update pool i ((pool i).filter p)
  have eq : (Fintype.piFinset pool).filter (fun x => p (x i)) = Fintype.piFinset pool' := by
    ext x
    simp only [mem_filter,Fintype.mem_piFinset]
    constructor
    · rintro ⟨hx,hi⟩ j
      by_cases e : j=i
      · subst j; simpa [pool'] using And.intro (hx i) hi
      · simpa [pool',e] using hx j
    · intro hx
      have at_i : x i ∈ pool i ∧ p (x i) := by simpa [pool'] using hx i
      refine ⟨fun j => ?_,at_i.2⟩
      by_cases e : j=i
      · subst j; exact at_i.1
      · simpa [pool',e] using hx j
  rw [eq,Fintype.card_piFinset,Fintype.card_piFinset,Nat.cast_prod,Nat.cast_prod,
    ← mul_prod_erase (univ : Finset I) _ (mem_univ i),
    ← mul_prod_erase (univ : Finset I) (fun j => ((pool j).card:ℝ)) (mem_univ i)]
  rw [show pool' i = (pool i).filter p by simp [pool']]
  have rest : (∏ j ∈ univ.erase i, ((pool' j).card:ℝ)) = ∏ j ∈ univ.erase i, ((pool j).card:ℝ) := by
    apply prod_congr rfl
    intro j hj
    simp [pool',(mem_erase.mp hj).1]
  rw [rest,← mul_assoc]
  exact mul_le_mul_of_nonneg_right h (prod_nonneg fun j _ => Nat.cast_nonneg (pool j).card)

omit [Fintype I] [DecidableEq I] in
theorem product_failures (A : Finset X) (B : Finset Y) (p₁ p₂ : X → Y → Prop) (a b : ℝ)
    (ref : ∀ y ∈ B, ((A.filter fun x => p₁ x y).card:ℝ) ≤ a*A.card)
    (row : ∀ x ∈ A, ((B.filter fun y => p₂ x y).card:ℝ) ≤ b*B.card) :
    (((A ×ˢ B).filter fun z => p₁ z.1 z.2 ∨ p₂ z.1 z.2).card:ℝ) ≤ (a+b)*(A ×ˢ B).card := by
  classical
  have point (x y) : (if p₁ x y ∨ p₂ x y then (1:ℝ) else 0) ≤
      (if p₁ x y then 1 else 0)+(if p₂ x y then 1 else 0) := by
    by_cases p : p₁ x y <;> by_cases q : p₂ x y <;> simp [p,q]
  rw [← sum_boole,sum_product,card_product,Nat.cast_mul]
  apply (sum_le_sum fun x _ => sum_le_sum fun y _ => point x y).trans
  simp only [sum_add_distrib]
  rw [sum_comm]
  simp only [sum_boole]
  have first := sum_le_sum (s:=B) ref
  have second := sum_le_sum (s:=A) row
  simp only [sum_const,nsmul_eq_mul] at first second
  linarith only [first,second]

end InducedDegreeRepetition.Edit
