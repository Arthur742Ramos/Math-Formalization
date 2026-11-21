module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

public section
namespace InducedDegreeRepetition.Sampling

open Finset
open scoped Classical
variable {I J X Y : Type*}

@[expose] noncomputable def mean [Fintype X] (f : X → ℝ) : ℝ :=
  (∑ x, f x)/Fintype.card X

theorem mean_equiv [Fintype X] [Fintype Y] (e : X ≃ Y) (f : X → ℝ) (g : Y → ℝ)
    (h : ∀ x, f x = g (e x)) : mean f = mean g := by
  unfold mean
  rw [Fintype.sum_equiv e f g h,Fintype.card_congr e]

theorem mean_const [Fintype X] [Nonempty X] (c : ℝ) : mean (fun _ : X => c) = c := by
  simp only [mean,sum_const,card_univ,nsmul_eq_mul]
  field_simp

theorem mean_prod [Fintype X] [Fintype Y] (f : X → Y → ℝ) :
    mean (fun p : X × Y => f p.1 p.2) = mean (fun x => mean (f x)) := by
  simp only [mean,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,← sum_div]
  ring

theorem mean_sum {K : Type*} [Fintype X] (s : Finset K) (f : K → X → ℝ) :
    mean (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, mean (f i) := by
  simp only [mean,← sum_div]
  rw [sum_comm]

theorem mean_le [Fintype X] (f g : X → ℝ) (h : ∀ x, f x ≤ g x) : mean f ≤ mean g :=
  div_le_div_of_nonneg_right (sum_le_sum (fun x _ => h x)) (Nat.cast_nonneg _)

/-- A product draw restricted to the image of an embedding is again uniform. -/
theorem mean_restrict [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Fintype X] [Nonempty X]
    (i : I ↪ J) (f : (I → X) → ℝ) :
    mean (fun x : J → X => f (fun k => x (i k))) = mean f := by
  classical
  let O := {j : J // j ∉ Set.range i}
  let select (x : J → X) := ((fun k => x (i k)),fun k : O => x k)
  let join (p : (I → X) × (O → X)) (j : J) :=
    if h : j ∈ Set.range i then p.1 h.choose else p.2 ⟨j,h⟩
  let e : (J → X) ≃ (I → X) × (O → X) :=
    ⟨select,join,fun x => funext fun j => by
      dsimp [join,select]; split <;> rename_i h
      · rw [h.choose_spec]
      · rfl,
     fun p => Prod.ext (funext fun k => by
       have h : i k ∈ Set.range i := ⟨k,rfl⟩
       simp only [select,join,dite_eq_left h]
       rw [i.injective h.choose_spec]) (funext fun k => by
       dsimp only [select,join]
       rw [dite_eq_right k.2])⟩
  have h := mean_equiv e (fun x : J → X => f (fun k => x (i k))) (fun p => f p.1) (fun _ => rfl)
  rw [h,mean_prod (fun x (_ : O → X) => f x)]
  simp only [mean_const]

end InducedDegreeRepetition.Sampling
