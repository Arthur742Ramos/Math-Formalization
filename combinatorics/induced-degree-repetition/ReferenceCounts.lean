module

public import GroupDeviation
public import JointDraw
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Sampling

open Finset
open scoped Classical
variable {X : Type*}

theorem absolute_tail [Fintype X] (f : X → ℝ) (v : ℝ) (pos : 0 < v) :
    mean (fun x => indicator (v < |f x|)) ≤ mean (fun x => f x^2)/v^2 := by
  have h := mean_markov (fun x => f x^2) (v^2) (by positivity) (fun _ => sq_nonneg _)
  convert h using 2
  funext x
  apply congrArg indicator
  apply propext
  simpa only [sq_abs] using (sq_lt_sq₀ pos.le (abs_nonneg (f x))).symm

theorem mean_bad_count {K Ω : Type*} [Fintype Ω] (S : Finset K) (p : K → Ω → Prop) :
    mean (fun x => ((S.filter fun k => p k x).card:ℝ)) = ∑ k ∈ S, mean (fun x => indicator (p k x)) := by
  classical
  simp only [indicator,← mean_sum,sum_boole]

/-- Count tester positions with an atypical contribution from at least one
reference group. This bound is established before parity selection. -/
theorem reference_bad_count {g s : ℕ} (R : Fin g → Type*) [∀ i, Fintype (R i)] [∀ i, Nonempty (R i)]
    [Fintype X] [Nonempty X] (error : (i : Fin g) → R i → X → ℝ) (v D : ℝ) (vp : 0 < v)
    (each : ∀ i, mean (fun y => mean (fun x => (error i x y)^2)) ≤ D) :
    mean (fun p : (∀ i, R i) × (Fin g → Fin s → X) =>
      ((univ.filter (fun k : Fin g × Fin s => ∃ i, v < |error i (p.1 i) (p.2 k.1 k.2)|)).card:ℝ)) ≤
      (g*s:ℕ)*(g*(D/v^2)) := by
  classical
  have swap := mean_bad_count (univ : Finset (Fin g × Fin s))
    (fun k (p : (∀ i, R i) × (Fin g → Fin s → X)) => ∃ i, v < |error i (p.1 i) (p.2 k.1 k.2)|)
  have one (k : Fin g × Fin s) (i : Fin g) : mean (fun p : (∀ i, R i) × (Fin g → Fin s → X) =>
      indicator (v < |error i (p.1 i) (p.2 k.1 k.2)|)) ≤ D/v^2 := by
    have a := absolute_tail (fun p : (∀ i, R i) × (Fin g → Fin s → X) => error i (p.1 i) (p.2 k.1 k.2)) v vp
    have marg := group_tester_mean (X:=X) R i k.1 k.2 (fun x y => error i x y^2)
    apply a.trans
    exact div_le_div_of_nonneg_right (marg.le.trans (each i)) (sq_nonneg _)
  have h := sum_le_sum (s:=(univ:Finset (Fin g × Fin s))) (fun k _ =>
    mean_union (fun i (z : (∀ i, R i) × (Fin g → Fin s → X)) => v < |error i (z.1 i) (z.2 k.1 k.2)|) _ (one k))
  convert swap.le.trans h using 1
  · apply congrArg mean
    funext p
    apply congrArg Nat.cast
    apply congrArg Finset.card
    ext k
    simp
  · simp [Fintype.card_prod]

end InducedDegreeRepetition.Sampling
