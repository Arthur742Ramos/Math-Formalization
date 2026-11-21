module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Restriction

open Finset
open scoped Classical
variable {X Y : Type*} [Fintype X]

/-- The number of complete sampled bipartite subgraphs with k ordered rows and m
ordered columns in V, allowing repeated vertices. -/
@[expose] noncomputable def moment (ok : X → Y → Prop) (m : ℕ) : ℕ → Finset Y → ℝ
  | 0,V => (V.card : ℝ)^m
  | k+1,V => ∑ x : X, moment ok m k (V.filter (ok x))

theorem moment_trivial (ok : X → Y → Prop) (m k : ℕ) (V : Finset Y) :
    moment ok m k V ≤ (Fintype.card X : ℝ)^k * (V.card:ℝ)^m := by
  induction k generalizing V with
  | zero => simp [moment]
  | succ k ih =>
    apply (sum_le_sum (s := (univ : Finset X)) fun x _ => (ih _).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (card_filter_le V (ok x))) m) (by positivity))).trans
    simp only [sum_const,card_univ,nsmul_eq_mul,pow_succ]
    apply le_of_eq; ring

theorem layer_moment (ok : X → Y → Prop) (m : ℕ) (V : Finset Y) (p b : ℝ)
    (hb : 0 ≤ b) (_hp : 0 ≤ p)
    (few : ((univ.filter (fun x => b*V.card < ((V.filter (ok x)).card:ℝ))).card:ℝ) ≤ p*Fintype.card X) :
    (∑ x, ((V.filter (ok x)).card : ℝ)^m) ≤
      (Fintype.card X:ℝ)*(p+b^m)*(V.card:ℝ)^m := by
  classical
  let E := univ.filter fun x => b*V.card < ((V.filter (ok x)).card:ℝ)
  have bound (x : X) : ((V.filter (ok x)).card:ℝ)^m ≤
      (b*V.card)^m + if x ∈ E then (V.card:ℝ)^m else 0 := by
    by_cases h : x ∈ E
    · rw [ite_eq_left h]
      exact (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (card_filter_le V _)) m).trans
        (le_add_of_nonneg_left (by positivity))
    · rw [ite_eq_right h,add_zero]
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      simpa [E] using h
  have h := sum_le_sum (s := (univ : Finset X)) fun x _ => bound x
  simp only [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,sum_ite_mem,univ_inter] at h
  simp only [mul_pow] at h
  have f : (E.card:ℝ) ≤ p*Fintype.card X := few
  exact h.trans (by nlinarith only [mul_le_mul_of_nonneg_right f (by positivity : (0:ℝ) ≤ (V.card:ℝ)^m)])

theorem moment_bound (ok : X → Y → Prop) (m k : ℕ) (U : Finset Y) (cut p b : ℝ)
    (hc : 0 ≤ cut) (hp : 0 ≤ p) (hb : 0 ≤ b)
    (sparse : ∀ V ⊆ U, cut ≤ V.card →
      ((univ.filter (fun x => b*V.card < ((V.filter (ok x)).card:ℝ))).card:ℝ) ≤ p*Fintype.card X) :
    ∀ V ⊆ U, moment ok m k V ≤ (Fintype.card X : ℝ)^k *
      ((p+b^m)^k*(V.card:ℝ)^m + cut^m) := by
  induction k with
  | zero => intro V _; simpa [moment] using (pow_nonneg hc m)
  | succ k ih =>
    intro V vu
    by_cases low : (V.card:ℝ) < cut
    · apply (moment_trivial ..).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (pow_le_pow_left₀ (Nat.cast_nonneg _) low.le m).trans
      exact le_add_of_nonneg_left (by positivity)
    · have h := sum_le_sum (s := (univ : Finset X)) fun x _ => ih (V.filter (ok x)) (filter_subset _ _ |>.trans vu)
      have e := layer_moment ok m V p b hb hp (sparse V vu (le_of_not_gt low))
      change (∑ x, moment ok m k (V.filter (ok x))) ≤ _
      apply h.trans
      simp only [← mul_sum,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,pow_succ]
      have mult := mul_le_mul_of_nonneg_left e (pow_nonneg (add_nonneg hp (pow_nonneg hb m)) k)
      apply le_trans _ (show (Fintype.card X:ℝ)^k *
        ((p+b^m)^k*((Fintype.card X:ℝ)*(p+b^m)*(V.card:ℝ)^m) + Fintype.card X*(cut^m)) ≤ _ by
        apply le_of_eq; ring)
      exact mul_le_mul_of_nonneg_left (add_le_add_left mult _) (by positivity)

end InducedDegreeRepetition.Restriction
