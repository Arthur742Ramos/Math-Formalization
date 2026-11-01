/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectBetaPath
public meta import LambdaTuring.DirectBetaPath

@[expose] public section

namespace LambdaTuring

theorem directPath_tail_lt (bit : Bool) (path : List Bool) :
    Encodable.encode path < Encodable.encode (bit :: path) := by
  rw [Encodable.encode_list_cons]
  have h := Nat.right_le_pair (Encodable.encode bit) (Encodable.encode path)
  omega

theorem directBetaChildKey_lt (child parent : Term) (hchild : directTermNumber child < directTermNumber parent)
    (bit : Bool) (path : List Bool) :
    Nat.pair (directTermNumber child) (Encodable.encode path) <
      Nat.pair (directTermNumber parent) (Encodable.encode (bit :: path)) := by
  have h₁ := Nat.pair_lt_pair_left (Encodable.encode path) hchild
  have h₂ := Nat.pair_lt_pair_right (directTermNumber parent) (directPath_tail_lt bit path)
  exact lt_trans h₁ h₂

def betaRootValue (term : Nat) : Nat :=
  let data := directPayload term
  let f := data.unpair.1
  let x := data.unpair.2
  if directTag term = 2 ∧ directTag f = 1 then
    Nat.succ (substValue x (Nat.pair (directPayload f) 0))
  else 0

theorem betaRootValue_correct (t : Term) :
    betaRootValue (directTermNumber t) = Encodable.encode ((betaAtPath [] t).map directTermNumber) := by
  cases t with
  | var n => simp [betaRootValue, directTag, directPayload, directTermNumber, betaAtPath]
  | abs t => simp [betaRootValue, directTag, directPayload, directTermNumber, betaAtPath]
  | app f x =>
    cases f with
    | var n => simp [betaRootValue, directTag, directPayload, directTermNumber, betaAtPath]
    | app f y => simp [betaRootValue, directTag, directPayload, directTermNumber, betaAtPath]
    | abs body =>
      simp [betaRootValue, directTag, directPayload, directTermNumber, betaAtPath, substValue_correct]

def betaHistoryRead (key child path : Nat) (history : List Nat) : Nat :=
  (history[(key - 1) - Nat.pair child path]?).getD 0

def betaWrapAbs (result : Nat) : Nat :=
  if result = 0 then 0 else Nat.succ (directAbsNumber result.pred)
def betaWrapLeft (result arg : Nat) : Nat :=
  if result = 0 then 0 else Nat.succ (directAppNumber result.pred arg)
def betaWrapRight (f result : Nat) : Nat :=
  if result = 0 then 0 else Nat.succ (directAppNumber f result.pred)

def betaPathStepValue (key : Nat) (history : List Nat) : Nat :=
  let term := key.unpair.1
  let path := key.unpair.2
  let tag := directTag term
  let data := directPayload term
  let direction := path.pred.unpair.1
  let rest := path.pred.unpair.2
  if path = 0 then betaRootValue term
  else if tag = 1 then
    if direction = 0 then betaWrapAbs (betaHistoryRead key data rest history) else 0
  else if tag = 2 then
    if direction = 0 then betaWrapLeft (betaHistoryRead key data.unpair.1 rest history) data.unpair.2
    else if direction = 1 then betaWrapRight data.unpair.1 (betaHistoryRead key data.unpair.2 rest history)
    else 0
  else 0

def betaPathHistory : Nat → List Nat
  | 0 => []
  | k + 1 => betaPathStepValue k (betaPathHistory k) :: betaPathHistory k

def betaPathValue (key : Nat) : Nat := betaPathStepValue key (betaPathHistory key)

theorem betaPathHistory_eq_course (context k : Nat) :
    courseHistory (fun _ n => betaPathValue n) context k = betaPathHistory k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change betaPathValue k :: courseHistory (fun _ n => betaPathValue n) context k =
      betaPathStepValue k (betaPathHistory k) :: betaPathHistory k
    rw [ih]
    rfl

theorem betaHistoryRead_correct (key child path : Nat) (h : Nat.pair child path < key) :
    betaHistoryRead key child path (betaPathHistory key) = betaPathValue (Nat.pair child path) := by
  have hread := courseHistory_lookup (fun _ n => betaPathValue n) 0 key (Nat.pair child path) h
  rw [betaPathHistory_eq_course] at hread
  simp [betaHistoryRead, hread]

theorem betaPathValue_correct (t : Term) (path : List Bool) :
    betaPathValue (Nat.pair (directTermNumber t) (Encodable.encode path)) =
      Encodable.encode ((betaAtPath path t).map directTermNumber) := by
  generalize hk : Nat.pair (directTermNumber t) (Encodable.encode path) = key
  induction key using Nat.strong_induction_on generalizing t path with
  | h key ih =>
    subst key
    cases path with
    | nil =>
      simpa [betaPathValue, betaPathStepValue] using betaRootValue_correct t
    | cons bit path =>
      cases t with
      | var n =>
        cases bit <;> simp [betaPathValue, betaPathStepValue, directTag,
          directTermNumber, betaAtPath, Encodable.encode_list_cons]
      | abs body =>
        cases bit with
        | true =>
          simp [betaPathValue, betaPathStepValue, directTag,
            directTermNumber, betaAtPath, Encodable.encode_list_cons]
        | false =>
          have hlt := directBetaChildKey_lt body (.abs body) (directTermNumber_abs_lt body) false path
          have hread := betaHistoryRead_correct (Nat.pair (directTermNumber (.abs body))
            (Encodable.encode (false :: path))) (directTermNumber body) (Encodable.encode path) hlt
          have hrec := ih (Nat.pair (directTermNumber body) (Encodable.encode path)) hlt body path rfl
          simp only [directTermNumber, Nat.succ_eq_add_one, Encodable.encode_list_cons] at hread
          simp only [show Encodable.encode false = 0 from rfl] at hread
          unfold betaPathValue
          cases hstep : betaAtPath path body <;>
            simp [betaPathStepValue, directTag, directPayload, directAbsNumber,
              directTermNumber, betaAtPath, Encodable.encode_list_cons, betaWrapAbs, hread, hrec, hstep]
      | app f x =>
        cases bit with
        | false =>
          have hlt := directBetaChildKey_lt f (.app f x) (directTermNumber_app_left_lt f x) false path
          have hread := betaHistoryRead_correct (Nat.pair (directTermNumber (.app f x))
            (Encodable.encode (false :: path))) (directTermNumber f) (Encodable.encode path) hlt
          have hrec := ih (Nat.pair (directTermNumber f) (Encodable.encode path)) hlt f path rfl
          simp only [directTermNumber, Nat.succ_eq_add_one, Encodable.encode_list_cons] at hread
          simp only [show Encodable.encode false = 0 from rfl] at hread
          unfold betaPathValue
          cases hstep : betaAtPath path f <;>
            simp [betaPathStepValue, directTag, directPayload, directAppNumber,
              directTermNumber, betaAtPath, Encodable.encode_list_cons, betaWrapLeft, hread, hrec, hstep]
        | true =>
          have hlt := directBetaChildKey_lt x (.app f x) (directTermNumber_app_right_lt f x) true path
          have hread := betaHistoryRead_correct (Nat.pair (directTermNumber (.app f x))
            (Encodable.encode (true :: path))) (directTermNumber x) (Encodable.encode path) hlt
          have hrec := ih (Nat.pair (directTermNumber x) (Encodable.encode path)) hlt x path rfl
          simp only [directTermNumber, Nat.succ_eq_add_one, Encodable.encode_list_cons] at hread
          simp only [show Encodable.encode true = 1 from rfl] at hread
          unfold betaPathValue
          cases hstep : betaAtPath path x <;>
            simp [betaPathStepValue, directTag, directPayload, directAppNumber,
              directTermNumber, betaAtPath, Encodable.encode_list_cons, betaWrapRight, hread, hrec, hstep]

#print axioms betaRootValue_correct
#print axioms betaPathValue_correct
end LambdaTuring
