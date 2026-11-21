module

public import PoolGroups
public import MeanEvents
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Sampling

open Finset OpenProblems
open scoped Classical
variable {V I : Type*} [Fintype I] [DecidableEq I]

/-- The squared error at one tester includes the sampling variance of the
reference tuples and the squared bias of the positional pools. -/
theorem reference_error (G : SimpleGraph V) (y : V) (p : ℝ) (L : ℕ) (len : I → ℕ)
    (pool : (i : I) → Fin (len i) → Finset V) (cap : ∀ i, len i ≤ L)
    [∀ i, Nonempty ↥(tupleSpace (List.ofFn (pool i)))] :
    mean (fun ref : ∀ i, tupleSpace (List.ofFn (pool i)) =>
      ((∑ i, (tupleDegree (adj G) y (ref i):ℝ))-p*(∑ i, len i))^2) ≤
      2*(Fintype.card I:ℝ)*L^2+2*(groupExpectation G len pool y-p*(∑ i, len i))^2 := by
  classical
  let P (i) := ↥(tupleSpace (List.ofFn (pool i)))
  let f (i) (x : P i) : ℝ := tupleDegree (adj G) y x
  let μ := groupExpectation G len pool y
  let b := μ-p*(∑ i, len i)
  have bound (i) (x : P i) : 0 ≤ f i x ∧ f i x ≤ L := by
    refine ⟨Nat.cast_nonneg _,Nat.cast_le.mpr ?_⟩
    have le : tupleDegree (adj G) y x.val ≤ x.val.length := List.countP_le_length ..
    exact le.trans ((Residues.tuple_len x.2).le.trans (by simpa using cap i))
  have var := variance_bound P univ f L (fun i _ x => bound i x)
  let err (x : ∀ i, P i) := ∑ i, (f i (x i)-mean (f i))
  have point (x : ∀ i, P i) : ((∑ i, f i (x i))-p*(∑ i, len i))^2 ≤ 2*err x^2+2*b^2 := by
    have eq : (∑ i, f i (x i))-p*(∑ i, len i) = err x + b := by
      simp only [err,sum_sub_distrib,b,μ,groupExpectation,f]
      ring
    rw [eq]
    nlinarith [sq_nonneg (err x-b)]
  apply (mean_le _ _ point).trans
  have split : mean (fun x : ∀ i, P i => 2*err x^2+2*b^2) = 2*mean (fun x => err x^2)+2*b^2 := by
    rw [show (fun x : ∀ i, P i => 2*err x^2+2*b^2) = fun x => 2*err x^2-(-(2*b^2)) by funext x; ring,
      mean_sub,mean_smul,mean_const]
    ring
  rw [split]
  change _ ≤ 2*(Fintype.card I:ℝ)*L^2+2*b^2
  have v : mean (fun x : ∀ i, P i => err x^2) ≤ (Fintype.card I:ℝ)*L^2 := by simpa only [card_univ] using var
  linarith

end InducedDegreeRepetition.Sampling
