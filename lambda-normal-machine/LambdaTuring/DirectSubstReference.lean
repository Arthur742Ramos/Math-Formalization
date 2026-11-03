/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectLiftByCode
public meta import LambdaTuring.DirectLiftByCode

@[expose] public section

namespace LambdaTuring

def substStepValue (value key : Nat) (history : List Nat) : Nat :=
  let term := key.unpair.1
  let depth := key.unpair.2
  let tag := directTag term
  let data := directPayload term
  if term ≤ depth then term
  else if tag = 0 then
    if data = depth then liftByValue depth value
    else directVarNumber (if depth < data then data - 1 else data)
  else if tag = 1 then directAbsNumber (liftChildValue key data (depth + 1) history)
  else if tag = 2 then directAppNumber
    (liftChildValue key data.unpair.1 depth history)
    (liftChildValue key data.unpair.2 depth history)
  else term

def substHistory (value : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => substStepValue value k (substHistory value k) :: substHistory value k

def substValue (value key : Nat) : Nat := substStepValue value key (substHistory value key)

theorem substHistory_eq_course (value k : Nat) :
    courseHistory (fun value n => substValue value n) value k = substHistory value k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change substValue value k :: courseHistory (fun value n => substValue value n) value k =
      substStepValue value k (substHistory value k) :: substHistory value k
    rw [ih]
    rfl

theorem substHistoryRead_correct (value key child depth : Nat) (h : Nat.pair child depth < key) :
    liftHistoryRead key child depth (substHistory value key) = substValue value (Nat.pair child depth) := by
  have hread := courseHistory_lookup (fun value n => substValue value n) value key (Nat.pair child depth) h
  rw [substHistory_eq_course] at hread
  simp [liftHistoryRead, hread]

theorem substValue_correct (t value : Term) (depth : Nat) :
    substValue (directTermNumber value) (Nat.pair (directTermNumber t) depth) =
      directTermNumber (substAt depth value t) := by
  generalize hk : Nat.pair (directTermNumber t) depth = key
  induction key using Nat.strong_induction_on generalizing t depth with
  | h key ih =>
    subst key
    by_cases hcut : directTermNumber t ≤ depth
    · simp [substValue, substStepValue, hcut, substAt_eq_self_of_code_le t depth value hcut]
    · cases t with
      | var n =>
        have hp := Nat.right_le_pair 0 n
        by_cases he : n = depth
        · subst n
          simp [substValue, substStepValue, directTag, directPayload, directTermNumber,
            substAt, liftByValue_correct]
          omega
        · by_cases hn : depth < n
          · simp [substValue, substStepValue, directTag, directPayload, directTermNumber,
              substAt, directVarNumber, he, hn]
            omega
          · simp [substValue, substStepValue, directTag, directPayload, directTermNumber,
              substAt, directVarNumber, he, hn]
      | abs t =>
        have hcut' : ¬ Nat.pair 1 (directTermNumber t) + 1 ≤ depth := by
          simpa [directTermNumber] using hcut
        by_cases hchild : directTermNumber t ≤ depth + 1
        · have hself := substAt_eq_self_of_code_le t (depth + 1) value hchild
          simp [substValue, substStepValue, directTag, directPayload, directAbsNumber,
            directTermNumber, substAt, hcut', liftChildValue, hchild, hself]
        · have hactive : depth + 1 < directTermNumber t := by omega
          have hlt := directAbsKey_lt t depth hactive
          have hread := substHistoryRead_correct (directTermNumber value) (Nat.pair (directTermNumber (.abs t)) depth)
            (directTermNumber t) (depth + 1) hlt
          have hrec := ih (Nat.pair (directTermNumber t) (depth + 1)) hlt t (depth + 1) rfl
          simp only [directTermNumber, Nat.succ_eq_add_one] at hread
          unfold substValue
          simp [substStepValue, directTag, directPayload, directAbsNumber,
            directTermNumber, substAt, hcut', liftChildValue, hchild, hread, hrec]
      | app f x =>
        have hcut' : ¬ Nat.pair 2 (Nat.pair (directTermNumber f) (directTermNumber x)) + 1 ≤ depth := by
          simpa [directTermNumber] using hcut
        have hf : liftChildValue (Nat.pair (directTermNumber (.app f x)) depth)
            (directTermNumber f) depth (substHistory (directTermNumber value) (Nat.pair (directTermNumber (.app f x)) depth)) =
            directTermNumber (substAt depth value f) := by
          by_cases hchild : directTermNumber f ≤ depth
          · simp [liftChildValue, hchild, substAt_eq_self_of_code_le f depth value hchild]
          · have hlt := directAppKey_left_lt f x depth
            have hread := substHistoryRead_correct (directTermNumber value) (Nat.pair (directTermNumber (.app f x)) depth)
              (directTermNumber f) depth hlt
            have hrec := ih (Nat.pair (directTermNumber f) depth) hlt f depth rfl
            simp [liftChildValue, hchild, hread, hrec]
        have hx : liftChildValue (Nat.pair (directTermNumber (.app f x)) depth)
            (directTermNumber x) depth (substHistory (directTermNumber value) (Nat.pair (directTermNumber (.app f x)) depth)) =
            directTermNumber (substAt depth value x) := by
          by_cases hchild : directTermNumber x ≤ depth
          · simp [liftChildValue, hchild, substAt_eq_self_of_code_le x depth value hchild]
          · have hlt := directAppKey_right_lt f x depth
            have hread := substHistoryRead_correct (directTermNumber value) (Nat.pair (directTermNumber (.app f x)) depth)
              (directTermNumber x) depth hlt
            have hrec := ih (Nat.pair (directTermNumber x) depth) hlt x depth rfl
            simp [liftChildValue, hchild, hread, hrec]
        simp only [directTermNumber, Nat.succ_eq_add_one] at hf hx
        simp [substValue, substStepValue, directTag, directPayload, directAppNumber,
          directTermNumber, substAt, hcut', hf, hx]

#print axioms substValue_correct
end LambdaTuring
