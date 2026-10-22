/- AI-assisted formalization under the repository Apache-2.0 license.
Source-level rational arithmetic ledger for the cached prefix scan. Each test
uses two multiplications and two subtractions; an advancing step additionally
uses two additions. Operand sizes, normalization, allocation, getters, sorting
and moment preprocessing are outside this ledger. No bit/runtime bound. -/
module
public import RationalPrefixScan
@[expose] public section
namespace SparseCompletion

def rationalPrefixArithmetic (M r δ Q H : ℚ) (xs : List (ℚ × ℚ)) :
    Bool × ℕ × ℕ :=
  (List.rec (motive := fun _ => ℚ → ℚ → Bool × ℕ × ℕ)
    (fun Q H => (decide (H-M*Q*(r-Q) ≤ δ), 1, 4))
    (fun a _ tail Q H =>
      if H-M*Q*(r-Q) ≤ δ then
        let out := tail (Q+a.1) (H+a.2)
        (out.1, out.2.1+1, out.2.2+6)
      else (false, 1, 4)) xs) Q H

theorem rational_prefix_arithmetic_projection (M r δ Q H : ℚ)
    (xs : List (ℚ × ℚ)) :
    ((rationalPrefixArithmetic M r δ Q H xs).1,
      (rationalPrefixArithmetic M r δ Q H xs).2.1) =
      rationalPrefixScan M r δ Q H xs := by
  induction xs generalizing Q H with
  | nil => rfl
  | cons a xs ih =>
    by_cases hc : H-M*Q*(r-Q) ≤ δ
    · simpa only [rationalPrefixArithmetic, rationalPrefixScan, ite_eq_left hc]
        using congrArg (fun out : Bool × ℕ => (out.1,out.2+1)) (ih (Q+a.1) (H+a.2))
    · simp [rationalPrefixArithmetic, rationalPrefixScan, hc]

theorem rational_prefix_arithmetic_ledger (M r δ Q H : ℚ)
    (xs : List (ℚ × ℚ)) :
    (rationalPrefixArithmetic M r δ Q H xs).2.2+2 =
      6*(rationalPrefixArithmetic M r δ Q H xs).2.1 := by
  induction xs generalizing Q H with
  | nil => rfl
  | cons a xs ih =>
    by_cases hc : H-M*Q*(r-Q) ≤ δ
    · simp only [rationalPrefixArithmetic, ite_eq_left hc]
      have hh := ih (Q+a.1) (H+a.2)
      simp only [rationalPrefixArithmetic] at hh
      omega
    · simp [rationalPrefixArithmetic, hc]

theorem rational_prefix_arithmetic_operations (M r δ Q H : ℚ)
    (xs : List (ℚ × ℚ)) :
    (rationalPrefixArithmetic M r δ Q H xs).2.2 ≤ 6*xs.length+4 := by
  induction xs generalizing Q H with
  | nil => simp [rationalPrefixArithmetic]
  | cons a xs ih =>
    by_cases hc : H-M*Q*(r-Q) ≤ δ
    · simp only [rationalPrefixArithmetic, ite_eq_left hc, List.length_cons]
      have hh := ih (Q+a.1) (H+a.2)
      simp only [rationalPrefixArithmetic] at hh
      omega
    · simp only [rationalPrefixArithmetic, ite_eq_right hc, List.length_cons]
      omega

theorem rational_prefix_arithmetic_comparisons (M r δ Q H : ℚ)
    (xs : List (ℚ × ℚ)) :
    (rationalPrefixArithmetic M r δ Q H xs).2.1 ≤ xs.length+1 := by
  have hh := congrArg Prod.snd (rational_prefix_arithmetic_projection M r δ Q H xs)
  change (rationalPrefixArithmetic M r δ Q H xs).2.1 =
    (rationalPrefixScan M r δ Q H xs).2 at hh
  rw [hh]
  exact rational_prefix_scan_comparisons M r δ Q H xs

end SparseCompletion
