/- AI-assisted formalization under the repository Apache-2.0 license.
An early-exit rational prefix scan carries both sums; its counter counts cut
comparisons, including the empty prefix, and excludes arithmetic bit cost. -/
module
public import ProtectedSources.RationalScoreSort
public import Mathlib.Algebra.BigOperators.Group.List.Basic
@[expose] public section
namespace SparseCompletion

def rationalPrefixScan (M r δ Q H : ℚ) : List (ℚ × ℚ) → Bool × ℕ
  | [] => (decide (H-M*Q*(r-Q) ≤ δ), 1)
  | a::xs =>
    if H-M*Q*(r-Q) ≤ δ then
      let out := rationalPrefixScan M r δ (Q+a.1) (H+a.2) xs
      (out.1, out.2+1)
    else (false, 1)

theorem rational_prefix_scan_comparisons (M r δ Q H : ℚ) (xs : List (ℚ × ℚ)) :
    (rationalPrefixScan M r δ Q H xs).2 ≤ xs.length+1 := by
  induction xs generalizing Q H with
  | nil => simp [rationalPrefixScan]
  | cons a xs ih =>
    simp only [rationalPrefixScan]
    split
    · have hi := ih (Q+a.1) (H+a.2)
      simp only [List.length_cons]
      omega
    · simp

theorem rational_prefix_scan_complete (M r δ Q H : ℚ) (xs : List (ℚ × ℚ)) :
    (rationalPrefixScan M r δ Q H xs).1 = true ↔
      ∀ l : ℕ, l ≤ xs.length →
        H+((xs.take l).map Prod.snd).sum-
          M*(Q+((xs.take l).map Prod.fst).sum)*
            (r-(Q+((xs.take l).map Prod.fst).sum)) ≤ δ := by
  induction xs generalizing Q H with
  | nil => simp [rationalPrefixScan]
  | cons a xs ih =>
    simp only [rationalPrefixScan]
    by_cases hc : H-M*Q*(r-Q) ≤ δ
    · rw [ite_eq_left hc]
      simp only [ih]
      constructor
      · intro hh l hl
        cases l with
        | zero => simpa using hc
        | succ l =>
          have hh' := hh l (by simpa using hl)
          simpa only [List.take_succ_cons, List.map_cons, List.sum_cons, add_assoc] using hh'
      · intro hh l hl
        have hh' := hh (l+1) (by simpa using hl)
        simpa only [List.take_succ_cons, List.map_cons, List.sum_cons, add_assoc] using hh'
    · rw [ite_eq_right hc]
      simp only [Bool.false_eq_true, false_iff]
      intro hh
      have hh' := hh 0 (Nat.zero_le _)
      exact hc (by simpa using hh')

end SparseCompletion
