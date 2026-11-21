module

public import LabelSamples
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Residues

open Finset
open scoped Classical
variable {P Y : Type*}

theorem agreement_lower (Q : Finset P) (E : Finset Y) (hne : E.Nonempty) (ok : P → Y → Prop)
    (ξ : ℝ) (hp : 0 < ξ) (hhalf : ξ ≤ 1/2) (n : ℕ)
    (high : ∀ y ∈ E, (1-ξ)*Q.card ≤ ((Q.filter fun p => ok p y).card:ℝ)) :
    Q.card/2 * ((1-2*ξ)*E.card)^n ≤ ∑ p ∈ Q, ((E.filter (ok p)).card:ℝ)^n := by
  classical
  let hits := fun p => ((E.filter (ok p)).card:ℝ)
  let rare := Q.filter fun p => hits p < (1-2*ξ)*E.card
  let good := Q.filter fun p => ¬ hits p < (1-2*ξ)*E.card
  have swap : (∑ p ∈ Q, hits p) = ∑ y ∈ E, ((Q.filter fun p => ok p y).card:ℝ) := by
    simp only [hits,← sum_boole]
    exact sum_comm
  have total := sum_le_sum (s := E) high
  rw [← swap,sum_const,nsmul_eq_mul] at total
  have h (p : P) (hQ : p ∈ Q) :
      2*ξ*E.card*(if p ∈ rare then (1:ℝ) else 0) ≤ E.card-hits p := by
    by_cases hr : p ∈ rare
    · rw [ite_eq_left hr,mul_one]
      have eq := (mem_filter.mp hr).2
      linarith
    · rw [ite_eq_right hr,mul_zero]
      exact sub_nonneg.mpr (Nat.cast_le.mpr (card_filter_le E (ok p)))
  have sum := sum_le_sum (s := Q) h
  simp only [← mul_sum,sum_sub_distrib,sum_const,nsmul_eq_mul,sum_ite_mem,
    mul_one] at sum
  rw [inter_eq_right.mpr (show rare ⊆ Q from filter_subset _ _)] at sum
  have epos : 0 < (E.card:ℝ) := by exact_mod_cast card_pos.mpr hne
  have rr : (rare.card:ℝ) ≤ Q.card/2 := by
    apply le_of_mul_le_mul_left (a := 2*ξ*E.card) _ (by positivity)
    nlinarith only [sum,total]
  have partition : (rare.card:ℝ)+good.card = Q.card := by exact_mod_cast card_filter_add_card_filter_not (s := Q) (fun p => hits p < (1-2*ξ)*E.card)
  have count : (Q.card:ℝ)/2 ≤ good.card := by linarith
  have base : 0 ≤ (1-2*ξ)*(E.card:ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  apply (mul_le_mul_of_nonneg_right count (pow_nonneg base n)).trans
  calc
    _ = ∑ _p ∈ good, ((1-2*ξ)*E.card)^n := by simp
    _ ≤ ∑ p ∈ good, (hits p)^n := sum_le_sum fun p h => pow_le_pow_left₀ base (le_of_not_gt (mem_filter.mp h).2) n
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => pow_nonneg (Nat.cast_nonneg _) _

theorem double_count (Q : Finset P) (E : Finset Y) (ok : P → Y → Prop) (n : ℕ) :
    (∑ ys ∈ Fintype.piFinset (fun _ : Fin n => E),
      ((Q.filter (fun p => ∀ i, ok p (ys i))).card:ℝ)) =
    ∑ p ∈ Q, ((E.filter (ok p)).card:ℝ)^n := by
  classical
  simp only [← sum_boole]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  have e : (Fintype.piFinset (fun _ : Fin n => E)).filter (fun ys => ∀ i, ok p (ys i)) =
      Fintype.piFinset (fun _ : Fin n => E.filter (ok p)) := by
    ext ys
    simp only [mem_filter,Fintype.mem_piFinset]
    exact ⟨fun h i => ⟨h.1 i,h.2 i⟩,fun h => ⟨fun i => (h i).1,fun i => (h i).2⟩⟩
  rw [sum_boole,e,Fintype.card_piFinset_const,Nat.cast_pow,sum_boole]

end InducedDegreeRepetition.Residues
