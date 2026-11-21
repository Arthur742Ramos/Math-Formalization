module

public import DualityRectangle
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Duality

open Finset
open scoped Classical
variable {X G : Type*} [Fintype X] [Nonempty X] [Fintype G]

@[expose] noncomputable def multiplicity (v : X → G) (x : G) := (univ.filter fun i => v i = x).card

omit [Nonempty X] in
theorem count_weight {R : Type*} [Semiring R] (v : X → G) (w : G → R) :
    (∑ x, (multiplicity v x : R) * w x) = ∑ i, w (v i) := by
  classical
  rw [← sum_fiberwise univ v (fun i => w (v i))]
  apply sum_congr rfl
  intro x _
  calc
    _ = ∑ _i ∈ univ.filter (fun i => v i = x), w x := by simp [multiplicity]
    _ = _ := sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2]

@[expose] noncomputable def empirical (v : X → G) : Law G where
  val x := (multiplicity v x : ℝ) / Fintype.card X
  nonneg _ := by positivity
  total := by
    have := count_weight v (fun _ => (1:ℝ))
    simp only [mul_one,sum_const,card_univ,nsmul_eq_mul] at this
    rw [← sum_div,this,div_self (by exact_mod_cast Fintype.card_ne_zero)]

theorem empirical_mass (v : X → G) (S : Finset G) :
    (∑ x ∈ S, empirical v x) * Fintype.card X = ((univ.filter (fun i => v i ∈ S)).card : ℝ) := by
  classical
  have hb : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  change (∑ x ∈ S, (multiplicity v x : ℝ) / Fintype.card X)*Fintype.card X = _
  rw [← sum_div,div_mul_cancel₀ _ hb]
  have e := count_weight v (fun x => if x ∈ S then (1:ℝ) else 0)
  simpa [mul_ite] using e

theorem empirical_average (v : X → G) (w : G → ℂ) :
    (Fintype.card X : ℂ) * average (empirical v) w = ∑ i, w (v i) := by
  have hb : (Fintype.card X : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← count_weight v w,average,mul_sum]
  apply sum_congr rfl
  intro x _
  change (Fintype.card X : ℂ) * (↑((multiplicity v x : ℝ) / Fintype.card X) * w x) = _
  push_cast
  field_simp

end InducedDegreeRepetition.Duality
