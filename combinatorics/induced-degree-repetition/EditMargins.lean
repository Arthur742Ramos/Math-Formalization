module

public import EditAllowed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section
namespace InducedDegreeRepetition.Edit

open Finset
open scoped Classical

/-- Summing rounded endpoints loses no part of the interior margin. -/
theorem target_margins {n : ℕ} (len : Fin n → ℕ) (θ : ℝ) (C d : ℕ)
    (margin : (C:ℝ) ≤ θ*(∑ i, len i)/2)
    (lo : θ*(∑ i, len i) ≤ d) (hi : (d:ℝ) ≤ (1-θ)*(∑ i, len i)) :
    (∑ i, (⌊θ*len i/5⌋:ℤ)) + C ≤ d ∧ (d:ℤ) ≤ (∑ i, (⌈(1-θ/5)*len i⌉:ℤ))-C := by
  have low := sum_le_sum (s:=(univ:Finset (Fin n))) (fun i _ => Int.floor_le (θ*len i/5))
  have high := sum_le_sum (s:=(univ:Finset (Fin n))) (fun i _ => Int.le_ceil ((1-θ/5)*len i))
  simp only [← sum_div,← mul_sum] at low high
  push_cast at margin lo hi
  have pos : 0 ≤ θ*(∑ i, (len i:ℝ)) := by linarith [Nat.cast_nonneg (α:=ℝ) C]
  constructor <;> apply (Int.cast_le (R:=ℝ)).mp <;> push_cast <;> linarith

theorem length_margin {n : ℕ} (len : Fin n → ℕ) (L C : ℕ) (θ : ℝ) (hθ : 0 < θ)
    (hl : 0 < L) (hnum : ⌈2*C/θ⌉₊ ≤ (univ.filter fun i => len i=L).card) :
    (C:ℝ) ≤ θ*(∑ i, len i)/2 := by
  let S := univ.filter fun i => len i=L
  have le : S.card ≤ ∑ i, len i := by
    calc
      _ = ∑ _i ∈ S, 1 := by simp
      _ ≤ ∑ i ∈ S, len i := sum_le_sum fun i hi => by rw [(mem_filter.mp hi).2]; omega
      _ ≤ _ := sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
  have cast : (⌈2*(C:ℝ)/θ⌉₊:ℝ) ≤ (∑ i, len i : ℕ) := Nat.cast_le.mpr (hnum.trans le)
  have h := (Nat.le_ceil (2*(C:ℝ)/θ)).trans cast
  have e := (div_le_iff₀ hθ).mp h
  push_cast at e ⊢
  linarith

end InducedDegreeRepetition.Edit
