/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.Explore
public meta import LambdaTuring.Explore

@[expose] public section

namespace LambdaTuring

def decodeChurchBody : Term → Option Nat
  | .var 0 => some 0
  | .app (.var 1) t => (decodeChurchBody t).map Nat.succ
  | _ => none

def decodeChurch : Term → Option Nat
  | .abs (.abs body) => decodeChurchBody body
  | _ => none

theorem decodeChurchBody_churchBody (n : Nat) : decodeChurchBody (churchBody n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [churchBody, decodeChurchBody, ih]

theorem decodeChurchBody_sound (t : Term) (n : Nat) :
    decodeChurchBody t = some n → t = churchBody n := by
  induction t generalizing n with
  | var i =>
    cases i with
    | zero => intro h; cases h; rfl
    | succ i => simp [decodeChurchBody]
  | abs t ih => simp [decodeChurchBody]
  | app f x ihf ihx =>
    cases f with
    | var i =>
      cases i with
      | zero => simp [decodeChurchBody]
      | succ i =>
        cases i with
        | zero =>
          change (decodeChurchBody x).map Nat.succ = some n → Term.app (.var 1) x = churchBody n
          rw [Option.map_eq_some_iff]
          rintro ⟨k, hk, rfl⟩
          simp [churchBody, ihx k hk]
        | succ i => simp [decodeChurchBody]
    | abs f => simp [decodeChurchBody]
    | app f g => simp [decodeChurchBody]

theorem decodeChurch_iff (t : Term) (n : Nat) : decodeChurch t = some n ↔ t = church n := by
  constructor
  · cases t with
    | var i => simp [decodeChurch]
    | app a b => simp [decodeChurch]
    | abs t =>
      cases t with
      | var i => simp [decodeChurch]
      | app a b => simp [decodeChurch]
      | abs body =>
        intro h
        exact congrArg (fun x => Term.abs (Term.abs x)) (decodeChurchBody_sound body n h)
  · intro h
    subst t
    exact decodeChurchBody_churchBody n

/-- All numeral indices observed among the paths of length at most `fuel`. -/
def observations (fuel : Nat) (t : Term) (n : Nat) : List Nat :=
  (explore fuel (.app t (church n))).filterMap decodeChurch

theorem mem_observations_iff (fuel : Nat) (t : Term) (n m : Nat) :
    m ∈ observations fuel t n ↔
      BoundedReaches fuel (.app t (church n)) (church m) := by
  simp [observations, List.mem_filterMap, decodeChurch_iff, mem_explore_iff]

theorem numericalResult_iff_observed (t : Term) (n m : Nat) :
    NumericalResult t n m ↔ ∃ fuel, m ∈ observations fuel t n := by
  simp only [NumericalResult, mem_observations_iff]
  constructor
  · exact reaches_bounded
  · rintro ⟨_, h⟩
    exact bounded_to_reaches h

#print axioms decodeChurch_iff
#print axioms numericalResult_iff_observed

end LambdaTuring
