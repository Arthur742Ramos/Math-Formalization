/- AI-assisted formalization under the repository Apache-2.0 license.
Intrinsic comparator-call ledger for merge; no bit-time claim.
Public list recursors avoid generated well-founded helper identities. Unit
thunks defer the unused branch, so building a recursor does not call le. -/
module
public import Mathlib.Data.List.Sort
@[expose] public section
namespace SparseCompletion

def countedMerge {α : Type*} (le : α → α → Bool) (xs ys : List α) : List α × ℕ :=
  List.rec (motive := fun _ => List α → List α × ℕ)
    (fun ys => (ys,0))
    (fun x xs recX ys =>
      (List.rec (motive := fun _ => Unit → List α × ℕ)
        (fun _ => (x::xs,0))
        (fun y ys recY _ =>
          if le x y then
            let r := recX (y::ys)
            (x::r.1,r.2+1)
          else
            let r := recY ()
            (y::r.1,r.2+1)) ys) ()) xs ys

theorem counted_merge_value {α : Type*} (le : α → α → Bool) (xs ys : List α) :
    (countedMerge le xs ys).1=List.merge xs ys le := by
  induction xs generalizing ys with
  | nil =>
    change ys = List.merge [] ys le
    exact (List.nil_merge ys).symm
  | cons x xs ih =>
    induction ys with
    | nil =>
      change x::xs = List.merge (x::xs) [] le
      exact (List.merge_right _).symm
    | cons y ys ihy =>
      have hc : countedMerge le (x::xs) (y::ys) =
          (if le x y then
            let r := countedMerge le xs (y::ys)
            (x::r.1,r.2+1)
          else
            let r := countedMerge le (x::xs) ys
            (y::r.1,r.2+1)) := rfl
      rw [hc,List.cons_merge_cons]
      by_cases h : le x y
      · simp only [ite_eq_left h]
        exact congrArg (List.cons x) (ih (y::ys))
      · simp only [ite_eq_right h]
        exact congrArg (List.cons y) ihy

theorem counted_merge_bound {α : Type*} (le : α → α → Bool) (xs ys : List α) :
    (countedMerge le xs ys).2 ≤ xs.length+ys.length := by
  induction xs generalizing ys with
  | nil =>
    change 0 ≤ _
    exact Nat.zero_le _
  | cons x xs ih =>
    induction ys with
    | nil =>
      change 0 ≤ _
      exact Nat.zero_le _
    | cons y ys ihy =>
      have hc : countedMerge le (x::xs) (y::ys) =
          (if le x y then
            let r := countedMerge le xs (y::ys)
            (x::r.1,r.2+1)
          else
            let r := countedMerge le (x::xs) ys
            (y::r.1,r.2+1)) := rfl
      rw [hc]
      by_cases h : le x y
      · simp only [ite_eq_left h]
        have hh := ih (y::ys)
        simp only [List.length_cons] at hh ⊢
        omega
      · simp only [ite_eq_right h]
        simp only [List.length_cons] at ihy ⊢
        omega

theorem counted_merge_length {α : Type*} (le : α → α → Bool) (xs ys : List α) :
    (countedMerge le xs ys).1.length=xs.length+ys.length := by
  rw [counted_merge_value]
  simp

end SparseCompletion
