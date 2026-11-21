module

public import IndependentVariance
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Sampling

open Finset
open scoped Classical
variable {X V I : Type*}

@[expose] noncomputable def indicator (p : Prop) : ℝ := if p then 1 else 0

theorem indicator_nonneg (p : Prop) : 0 ≤ indicator p := by dsimp [indicator]; split <;> norm_num

theorem event_mean (S : Finset X) (p : X → Prop) :
    mean (fun x : S => indicator (p x)) = ((S.filter p).card:ℝ)/S.card := by
  classical
  unfold mean
  rw [Fintype.card_coe]
  congr 1
  rw [← sum_subtype (F:= (inferInstance : Fintype S)) S (fun _ => Iff.rfl) (fun x => indicator (p x))]
  simp [indicator]

theorem mean_markov [Fintype X] (f : X → ℝ) (t : ℝ) (ht : 0 < t) (nn : ∀ x, 0 ≤ f x) :
    mean (fun x => indicator (t < f x)) ≤ mean f/t := by
  rw [le_div_iff₀ ht]
  rw [mul_comm,← mean_smul]
  apply mean_le
  intro x
  by_cases h : t < f x
  · simpa [indicator,h] using h.le
  · simpa [indicator,h] using nn x

theorem product_event_bound [Fintype I] [DecidableEq I] {J : Type*} [Fintype J] [DecidableEq J]
    (S : I → Finset X) (T : J → Finset V) (p : (I → X) → (J → V) → Prop) (ε : ℝ) (he : 0 ≤ ε)
    (h : ((((Fintype.piFinset S) ×ˢ (Fintype.piFinset T)).filter fun z => p z.1 z.2).card:ℝ) ≤
      ε*((Fintype.piFinset S) ×ˢ (Fintype.piFinset T)).card) :
    mean (fun z : (∀ i, S i) × (∀ j, T j) => indicator (p (fun i => z.1 i) (fun j => z.2 j))) ≤ ε := by
  classical
  let A := Fintype.piFinset S
  let B := Fintype.piFinset T
  let e : ((∀ i, S i) × (∀ j, T j)) ≃ ↥(A ×ˢ B) := {
    toFun z := ⟨(fun i => z.1 i,fun j => z.2 j),mem_product.mpr
      ⟨Fintype.mem_piFinset.mpr fun i => (z.1 i).2,Fintype.mem_piFinset.mpr fun j => (z.2 j).2⟩⟩
    invFun z := (fun i => ⟨z.val.1 i,Fintype.mem_piFinset.mp (mem_product.mp z.2).1 i⟩,
      fun j => ⟨z.val.2 j,Fintype.mem_piFinset.mp (mem_product.mp z.2).2 j⟩)
    left_inv _ := rfl
    right_inv _ := rfl }
  have eq := mean_equiv e (fun z : (∀ i, S i) × (∀ j, T j) => indicator (p (fun i => z.1 i) (fun j => z.2 j))) (fun z => indicator (p z.val.1 z.val.2)) (fun _ => rfl)
  rw [eq,event_mean (A ×ˢ B) (fun z => p z.1 z.2)]
  by_cases pos : 0 < (A ×ˢ B).card
  · exact (div_le_iff₀ (by exact_mod_cast pos : (0:ℝ)<(A ×ˢ B).card)).mpr h
  · simp [Nat.eq_zero_of_not_pos pos,he]

end InducedDegreeRepetition.Sampling
