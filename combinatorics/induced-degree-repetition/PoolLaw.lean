module

public import MixedLaws
public import DualityRows
public import CountRange
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

public section
namespace InducedDegreeRepetition.Duality

open Finset Law
open scoped Classical
variable {G X : Type*} [Fintype G] [AddCommGroup G]

/-- The empirical image of a positional pool. For an empty pool its unnormalized
tuple count is zero, so the default point law has no effect on the count. -/
@[expose] noncomputable def poolLaw (v : X → G) (S : Finset X) : Law G :=
  if h : S.Nonempty then
    let _ : Nonempty S := h.to_subtype
    empirical (fun x : S => v x)
  else point 0

theorem pool_test (v : X → G) (S : Finset X) (w : G → ℝ) :
    (S.card:ℝ)*(∑ z, poolLaw v S z*w z) = ∑ x ∈ S, w (v x) := by
  classical
  by_cases h : S.Nonempty
  · let : Nonempty S := h.to_subtype
    rw [poolLaw,dite_eq_left h,mul_sum,sum_subtype (F := (inferInstance : Fintype S)) S (fun _ => Iff.rfl)]
    rw [← count_weight (R := ℝ) (fun x : S => v x) w]
    apply sum_congr rfl
    intro z _
    change (S.card:ℝ)*((multiplicity (fun x : S => v x) z : ℝ)/Fintype.card S*w z) = _
    rw [Fintype.card_coe]
    field_simp [Nat.cast_ne_zero.mpr (card_pos.mpr h).ne']
  · simp [not_nonempty_iff_eq_empty.mp h]

theorem pool_mass (v : X → G) (S : Finset X) (p : G → Prop) :
    S.card*massOn (poolLaw v S) {z | p z} = ((S.filter fun x => p (v x)).card:ℝ) := by
  have h := pool_test v S (fun z => if p z then (1:ℝ) else 0)
  simp only [massOn,Set.mem_ofPred_eq]
  simpa [mul_ite] using h

@[expose] def vectorSum (v : X → G) (l : List X) := (l.map v).sum

theorem tuple_test (v : X → G) (l : List (Finset X)) (w : G → ℝ) :
    (∑ P ∈ tupleSpace l, w (vectorSum v P)) =
      (tupleSpace l).card * ∑ z, listSum (l.map (poolLaw v)) z*w z := by
  induction l generalizing w with
  | nil => simp [tupleSpace,vectorSum,listSum,point,ite_mul]
  | cons S l ih =>
    let g := listSum (l.map (poolLaw v))
    change _ = _*(∑ z, ((poolLaw v S).plus g) z*w z)
    rw [plus_test]
    simp only [tupleSpace,List.foldr_cons,sum_map,sum_product,Function.Embedding.coeFn_mk,
      vectorSum,List.map_cons,List.sum_cons,card_map,card_product,Nat.cast_mul]
    change (∑ x ∈ S, ∑ P ∈ tupleSpace l, w (v x+vectorSum v P)) =
      ((S.card:ℝ)*(tupleSpace l).card) * ∑ z, poolLaw v S z*∑ y, g y*w (z+y)
    have step (x : X) := ih (fun z => w (v x+z))
    simp_rw [step,← mul_sum]
    have avg := pool_test v S (fun z => ∑ y, g y * w (z+y))
    rw [← avg]
    ring

theorem tuple_atom (v : X → G) (l : List (Finset X)) (t : G) :
    (((tupleSpace l).filter fun P => vectorSum v P = t).card : ℝ) =
      (tupleSpace l).card * listSum (l.map (poolLaw v)) t := by
  simpa [mul_ite] using tuple_test v l (fun z => if z=t then (1:ℝ) else 0)

end InducedDegreeRepetition.Duality
