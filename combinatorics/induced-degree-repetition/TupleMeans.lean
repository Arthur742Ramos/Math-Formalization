module

public import RegisteredProfiles
public import UniformMean
public import FourthMoment
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

public section
namespace InducedDegreeRepetition.Sampling

open Finset OpenProblems
open scoped Classical
variable {V : Type*}

theorem tuple_sum_expectation (s : List (Finset V)) (v : V → ℝ) :
    (∑ P ∈ tupleSpace s, (P.map v).sum) = (tupleSpace s).card*
      (s.map (fun (U : Finset V) => mean (fun x : U => v x))).sum := by
  classical
  induction s with
  | nil => simp [tupleSpace]
  | cons U s ih =>
    have h : (U.card:ℝ)*mean (fun x : U => v x) = ∑ x ∈ U, v x := by
      by_cases en : U.Nonempty
      · rw [mean,Fintype.card_coe,← sum_subtype U (fun _ => Iff.rfl) v]
        field_simp
      · simp [not_nonempty_iff_eq_empty.mp en]
    simp only [tupleSpace,List.foldr_cons,sum_map,sum_product,Function.Embedding.coeFn_mk,List.map_cons,
      List.sum_cons,sum_add_distrib,sum_const,nsmul_eq_mul,card_map,card_product,Nat.cast_mul]
    change (∑ x ∈ U, (tupleSpace s).card*v x) + (U.card:ℝ)*(∑ P ∈ tupleSpace s, (P.map v).sum) = _
    rw [← mul_sum,← h,ih]
    unfold tupleSpace; ring

theorem degree_as_sum (G : SimpleGraph V) (y : V) (P : List V) :
    (tupleDegree (adj G) y P : ℝ) = (P.map (fun v => if G.Adj y v then (1:ℝ) else 0)).sum := by
  induction P with
  | nil => simp [tupleDegree]
  | cons x P ih =>
    by_cases h : G.Adj y x <;> simpa [tupleDegree,adj,List.countP_cons,h,add_comm] using ih

theorem mean_tuple_degree (G : SimpleGraph V) (y : V) (s : List (Finset V)) (hn : (tupleSpace s).Nonempty) :
    mean (fun P : tupleSpace s => (tupleDegree (adj G) y P:ℝ)) =
      (s.map (fun (U : Finset V) => mean (fun x : U => if G.Adj y x then (1:ℝ) else 0))).sum := by
  classical
  rw [mean]
  rw [Fintype.card_coe,← sum_subtype (tupleSpace s) (fun _ => Iff.rfl) (fun P => (tupleDegree (adj G) y P:ℝ))]
  simp_rw [degree_as_sum]
  rw [tuple_sum_expectation, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (card_pos.mpr hn).ne')]

theorem pool_mean (G : SimpleGraph V) (p : ℝ) (y : V) (U : Finset V) (b : ℕ) (sz : U.card=b)
    (hb : 0 < b) :
    (b:ℝ)*(mean (fun x : U => if G.Adj y x then (1:ℝ) else 0)-p) = ∑ x ∈ U, centered G p y x := by
  classical
  rw [mean,Fintype.card_coe,sz,← sum_subtype U (fun _ => Iff.rfl) (fun x => if G.Adj y x then (1:ℝ) else 0)]
  simp only [centered,sum_sub_distrib,sum_const,nsmul_eq_mul,sz]
  field_simp

end InducedDegreeRepetition.Sampling
