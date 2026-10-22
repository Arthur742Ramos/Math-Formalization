/- AI-assisted formalization under the repository Apache-2.0 license.
A returned first failing prefix length with the same cached rational scan.
The intrinsic ledger counts comparisons, not arithmetic or bit operations. -/
module
public import RationalPrefixScan
@[expose] public section
namespace SparseCompletion

def rationalViolationSearch (M r δ Q H : ℚ) (xs : List (ℚ × ℚ)) : Option ℕ × ℕ :=
  (List.rec (motive := fun _ => ℚ → ℚ → Option ℕ × ℕ)
    (fun Q H => (if H-M*Q*(r-Q) ≤ δ then none else some 0, 1))
    (fun a _ tail Q H =>
      if H-M*Q*(r-Q) ≤ δ then
        let out := tail (Q+a.1) (H+a.2)
        (out.1.map Nat.succ, out.2+1)
      else (some 0, 1)) xs) Q H

theorem rational_violation_search_none_iff (M r δ Q H : ℚ) (xs : List (ℚ × ℚ)) :
    (rationalViolationSearch M r δ Q H xs).1 = none ↔
      (rationalPrefixScan M r δ Q H xs).1 = true := by
  induction xs generalizing Q H with
  | nil =>
    by_cases hc : H-M*Q*(r-Q) ≤ δ
    · simp [rationalViolationSearch, rationalPrefixScan, hc]
    · simp [rationalViolationSearch, rationalPrefixScan, hc]
  | cons a xs ih =>
    by_cases hc : H-M*Q*(r-Q) ≤ δ
    · simp only [rationalViolationSearch, rationalPrefixScan, ite_eq_left hc]
      exact Option.map_eq_none_iff.trans (ih (Q+a.1) (H+a.2))
    · simp [rationalViolationSearch, rationalPrefixScan, hc]

theorem rational_violation_search_count (M r δ Q H : ℚ) (xs : List (ℚ × ℚ)) :
    (rationalViolationSearch M r δ Q H xs).2 =
      (rationalPrefixScan M r δ Q H xs).2 := by
  induction xs generalizing Q H with
  | nil => simp [rationalViolationSearch, rationalPrefixScan]
  | cons a xs ih =>
    by_cases hc : H-M*Q*(r-Q) ≤ δ
    · simp only [rationalViolationSearch, rationalPrefixScan, ite_eq_left hc]
      exact congrArg (fun n : ℕ => n+1) (ih (Q+a.1) (H+a.2))
    · simp [rationalViolationSearch, rationalPrefixScan, hc]

theorem rational_violation_search_comparisons (M r δ Q H : ℚ) (xs : List (ℚ × ℚ)) :
    (rationalViolationSearch M r δ Q H xs).2 ≤ xs.length+1 := by
  rw [rational_violation_search_count]
  exact rational_prefix_scan_comparisons M r δ Q H xs

theorem rational_violation_search_some_sound (M r δ Q H : ℚ) (xs : List (ℚ × ℚ))
    (l : ℕ) (hout : (rationalViolationSearch M r δ Q H xs).1 = some l) :
    l ≤ xs.length ∧
      δ < H+((xs.take l).map Prod.snd).sum-
        M*(Q+((xs.take l).map Prod.fst).sum)*
          (r-(Q+((xs.take l).map Prod.fst).sum)) := by
  induction xs generalizing Q H l with
  | nil =>
    by_cases hc : H-M*Q*(r-Q) ≤ δ
    · simp only [rationalViolationSearch, ite_eq_left hc] at hout
      cases hout
    · simp only [rationalViolationSearch, ite_eq_right hc] at hout
      have hl : 0 = l := Option.some.inj hout
      subst l
      exact ⟨Nat.zero_le _, by simpa using lt_of_not_ge hc⟩
  | cons a xs ih =>
    by_cases hc : H-M*Q*(r-Q) ≤ δ
    · simp only [rationalViolationSearch, ite_eq_left hc] at hout
      obtain ⟨j,hj,hjl⟩ := Option.map_eq_some_iff.mp hout
      obtain ⟨hbound,hbad⟩ := ih (Q+a.1) (H+a.2) j hj
      subst l
      refine ⟨by simpa using Nat.succ_le_succ hbound, ?_⟩
      simpa only [List.take_succ_cons, List.map_cons, List.sum_cons, add_assoc] using hbad
    · simp only [rationalViolationSearch, ite_eq_right hc] at hout
      have hl : 0 = l := Option.some.inj hout
      subst l
      exact ⟨Nat.zero_le _, by simpa using lt_of_not_ge hc⟩

theorem rational_violation_search_none_iff_prefixes (M r δ Q H : ℚ)
    (xs : List (ℚ × ℚ)) :
    (rationalViolationSearch M r δ Q H xs).1 = none ↔
      ∀ l : ℕ, l ≤ xs.length →
        H+((xs.take l).map Prod.snd).sum-
          M*(Q+((xs.take l).map Prod.fst).sum)*
            (r-(Q+((xs.take l).map Prod.fst).sum)) ≤ δ :=
  (rational_violation_search_none_iff M r δ Q H xs).trans
    (rational_prefix_scan_complete M r δ Q H xs)

end SparseCompletion
