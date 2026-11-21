module

public import SampleCount
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Positivity

public section
namespace InducedDegreeRepetition.Restriction

open Finset
open scoped Classical
variable {I J X Y : Type} [DecidableEq I] [DecidableEq J] [Fintype I] [Fintype J] [Fintype X] [Fintype Y]

theorem split_sum (S : Finset I) (f : (S → X) → ({i : I // i ∉ S} → X) → ℝ) :
    (∑ xs : I → X, f (fun i => xs i) (fun i => xs i)) = ∑ a, ∑ b, f a b := by
  classical
  rw [← Fintype.sum_prod_type (fun p : (S → X) × ({i : I // i ∉ S} → X) => f p.1 p.2)]
  apply Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => X))
  intro xs
  rfl

set_option maxHeartbeats 1600000 in
/-- Exposing the designated row and column labels leaves uniform independent
draws on all other positions. -/
theorem designated_sum (R : Finset I) (C : Finset J) (ok : (R → X) → (C → Y) → X → Y → Prop) :
    (∑ xs : I → X, ∑ ys : J → Y, if ∀ (i : {i : I // i ∉ R}) (j : {j : J // j ∉ C}),
      ok (fun i => xs i) (fun j => ys j) (xs i) (ys j) then (1:ℝ) else 0) =
    ∑ a : R → X, ∑ b : C → Y, samples {i : I // i ∉ R} {j : J // j ∉ C} (ok a b) := by
  classical
  let w (a : R → X) (x : {i : I // i ∉ R} → X) (b : C → Y) (y : {j : J // j ∉ C} → Y) :=
    if ∀ i j, ok a b (x i) (y j) then (1:ℝ) else 0
  change (∑ xs : I → X, ∑ ys : J → Y, w (fun i => xs i) (fun i => xs i) (fun j => ys j) (fun j => ys j)) = _
  apply Eq.trans (split_sum R (fun a x => ∑ ys : J → Y, w a x (fun j => ys j) (fun j => ys j)))
  apply sum_congr rfl
  intro a _
  calc
    _ = ∑ x, ∑ b, ∑ y, w a x b y := sum_congr rfl fun x _ => split_sum C (w a x)
    _ = ∑ b, ∑ x, ∑ y, w a x b y := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro b _
      unfold samples
      apply sum_congr (Finset.ext fun _ => by simp)
      intro x _
      apply sum_congr (Finset.ext fun _ => by simp)
      intro y _
      by_cases h : ∀ i j, ok a b (x i) (y j) <;> simp only [w,h,ite_false]

/-- Sum an event bound over the choices of both sets of designated positions.
The conditional model is allowed to depend on their values. -/
theorem compression_count (good : (I → X) → (J → Y) → Prop)
    (T : Finset I → Finset J → Prop)
    (ok : (R : Finset I) → (C : Finset J) → (R → X) → (C → Y) → X → Y → Prop)
    (witness : ∀ xs ys, good xs ys → ∃ R C, T R C ∧
      ∀ (i : {i : I // i ∉ R}) (j : {j : J // j ∉ C}),
      ok R C (fun i => xs i) (fun j => ys j) (xs i) (ys j))
    (F : ℝ) (hF : 0 ≤ F) (bound : ∀ R C, T R C → ∀ (a : R → X) (b : C → Y),
      samples {i : I // i ∉ R} {j : J // j ∉ C} (ok R C a b) ≤
        F * Fintype.card ({i : I // i ∉ R} → X) * Fintype.card ({j : J // j ∉ C} → Y)) :
    (∑ xs, ∑ ys, if good xs ys then (1:ℝ) else 0) ≤
      (2:ℝ)^Fintype.card I * 2^Fintype.card J * F * Fintype.card (I → X) * Fintype.card (J → Y) := by
  classical
  let flag (R : Finset I) (C : Finset J) (xs : I → X) (ys : J → Y) :=
    if T R C ∧ ∀ (i : {i : I // i ∉ R}) (j : {j : J // j ∉ C}),
       ok R C (fun i => xs i) (fun j => ys j) (xs i) (ys j) then (1:ℝ) else 0
  have nn R C xs ys : 0 ≤ flag R C xs ys := by dsimp [flag]; split <;> norm_num
  have single (xs : I → X) (ys : J → Y) : (if good xs ys then (1:ℝ) else 0) ≤ ∑ R, ∑ C, flag R C xs ys := by
    by_cases hg : good xs ys
    · obtain ⟨R,C,h,yes⟩ := witness xs ys hg
      rw [ite_eq_left hg]
      apply le_trans _ (single_le_sum (fun r _ => sum_nonneg fun c _ => nn r c xs ys) (mem_univ R))
      apply le_trans _ (single_le_sum (fun c _ => nn R c xs ys) (mem_univ C))
      simp only [flag,ite_eq_left (And.intro h yes),le_refl]
    · simpa [hg] using sum_nonneg (s := (univ : Finset (Finset I))) fun r _ => sum_nonneg fun c _ => nn r c xs ys
  have splitCard {A B : Type} [DecidableEq A] [Fintype A] [Fintype B] (S : Finset A) :
      (Fintype.card (S → B):ℝ) * Fintype.card ({i : A // i ∉ S} → B) = Fintype.card (A → B) := by
    exact_mod_cast (Fintype.card_prod _ _).symm.trans
      (Fintype.card_congr (Equiv.piEquivPiSubtypeProd (fun i : A => i ∈ S) (fun _ => B))).symm
  let total := F * Fintype.card (I → X) * Fintype.card (J → Y)
  have each (R : Finset I) (C : Finset J) : (∑ xs, ∑ ys, flag R C xs ys) ≤ total := by
    by_cases h : T R C
    · simp only [flag,h,true_and,designated_sum]
      apply le_trans (sum_le_sum fun a _ => sum_le_sum fun b _ => bound R C h a b)
      simp only [sum_const,card_univ,nsmul_eq_mul]
      dsimp [total]
      rw [← splitCard (B := X) R,← splitCard (B := Y) C]
      apply le_of_eq
      ring
    · simp only [flag,h,false_and,ite_false,sum_const_zero]
      dsimp [total]; positivity
  apply le_trans (sum_le_sum fun x _ => sum_le_sum fun y _ => single x y)
  calc
    _ = ∑ R, ∑ C, ∑ xs, ∑ ys, flag R C xs ys := by
      simp_rw [sum_comm (f := fun ys R => ∑ C, flag R C _ ys)]
      rw [sum_comm]
      apply sum_congr rfl
      intro R _
      simp_rw [sum_comm (f := fun ys C => flag R C _ ys)]
      rw [sum_comm]
    _ ≤ ∑ _R : Finset I, ∑ _C : Finset J, total := sum_le_sum fun R _ => sum_le_sum fun C _ => each R C
    _ = _ := by simp [total]; ring

end InducedDegreeRepetition.Restriction
