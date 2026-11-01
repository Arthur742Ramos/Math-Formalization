/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectTermBounds
public meta import LambdaTuring.DirectTermBounds

@[expose] public section

namespace LambdaTuring

def directTag (term : Nat) : Nat := term.pred.unpair.1
def directPayload (term : Nat) : Nat := term.pred.unpair.2
def directVarNumber (n : Nat) : Nat := Nat.succ (Nat.pair 0 n)
def directAbsNumber (body : Nat) : Nat := Nat.succ (Nat.pair 1 body)
def directAppNumber (f x : Nat) : Nat := Nat.succ (Nat.pair 2 (Nat.pair f x))

def liftHistoryRead (key child depth : Nat) (history : List Nat) : Nat :=
  (history[(key - 1) - Nat.pair child depth]?).getD 0

def liftChildValue (key child depth : Nat) (history : List Nat) : Nat :=
  if child ≤ depth then child else liftHistoryRead key child depth history

def liftStepValue (key : Nat) (history : List Nat) : Nat :=
  let term := key.unpair.1
  let depth := key.unpair.2
  let tag := directTag term
  let data := directPayload term
  if term ≤ depth then term
  else if tag = 0 then directVarNumber (if depth ≤ data then data + 1 else data)
  else if tag = 1 then directAbsNumber (liftChildValue key data (depth + 1) history)
  else if tag = 2 then directAppNumber
    (liftChildValue key data.unpair.1 depth history)
    (liftChildValue key data.unpair.2 depth history)
  else term

def liftHistory : Nat → List Nat
  | 0 => []
  | k + 1 => liftStepValue k (liftHistory k) :: liftHistory k

def liftValue (key : Nat) : Nat := liftStepValue key (liftHistory key)

theorem liftHistory_eq_course (context k : Nat) :
    courseHistory (fun _ n => liftValue n) context k = liftHistory k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change liftValue k :: courseHistory (fun _ n => liftValue n) context k =
      liftStepValue k (liftHistory k) :: liftHistory k
    rw [ih]
    rfl

theorem liftHistoryRead_correct (key child depth : Nat) (h : Nat.pair child depth < key) :
    liftHistoryRead key child depth (liftHistory key) = liftValue (Nat.pair child depth) := by
  have hread := courseHistory_lookup (fun _ n => liftValue n) 0 key (Nat.pair child depth) h
  rw [liftHistory_eq_course] at hread
  simp [liftHistoryRead, hread]

theorem liftValue_correct (t : Term) (depth : Nat) :
    liftValue (Nat.pair (directTermNumber t) depth) = directTermNumber (liftFrom depth t) := by
  generalize hk : Nat.pair (directTermNumber t) depth = key
  induction key using Nat.strong_induction_on generalizing t depth with
  | h key ih =>
    subst key
    by_cases hcut : directTermNumber t ≤ depth
    · simp [liftValue, liftStepValue, hcut, liftFrom_eq_self_of_code_le t depth hcut]
    · cases t with
      | var n =>
        by_cases hn : depth ≤ n
        · have hp := Nat.right_le_pair 0 n
          simp [liftValue, liftStepValue, directTag, directPayload, directVarNumber,
            directTermNumber, liftFrom, hn, Nat.not_lt_of_ge hn]
          omega
        · have hn' : n < depth := by omega
          simp [liftValue, liftStepValue, directTag, directPayload, directVarNumber,
            directTermNumber, liftFrom, hn, hn']
      | abs t =>
        have hcut' : ¬ Nat.pair 1 (directTermNumber t) + 1 ≤ depth := by
          simpa [directTermNumber] using hcut
        by_cases hchild : directTermNumber t ≤ depth + 1
        · have hself := liftFrom_eq_self_of_code_le t (depth + 1) hchild
          simp [liftValue, liftStepValue, directTag, directPayload, directAbsNumber,
            directTermNumber, liftFrom, hcut', liftChildValue, hchild, hself]
        · have hactive : depth + 1 < directTermNumber t := by omega
          have hlt := directAbsKey_lt t depth hactive
          have hread := liftHistoryRead_correct (Nat.pair (directTermNumber (.abs t)) depth)
            (directTermNumber t) (depth + 1) hlt
          have hrec := ih (Nat.pair (directTermNumber t) (depth + 1)) hlt t (depth + 1) rfl
          simp only [directTermNumber, Nat.succ_eq_add_one] at hread
          unfold liftValue
          simp [liftStepValue, directTag, directPayload, directAbsNumber,
            directTermNumber, liftFrom, hcut', liftChildValue, hchild, hread, hrec]
      | app f x =>
        have hcut' : ¬ Nat.pair 2 (Nat.pair (directTermNumber f) (directTermNumber x)) + 1 ≤ depth := by
          simpa [directTermNumber] using hcut
        have hf : liftChildValue (Nat.pair (directTermNumber (.app f x)) depth)
            (directTermNumber f) depth (liftHistory (Nat.pair (directTermNumber (.app f x)) depth)) =
            directTermNumber (liftFrom depth f) := by
          by_cases hchild : directTermNumber f ≤ depth
          · simp [liftChildValue, hchild, liftFrom_eq_self_of_code_le f depth hchild]
          · have hlt := directAppKey_left_lt f x depth
            have hread := liftHistoryRead_correct (Nat.pair (directTermNumber (.app f x)) depth)
              (directTermNumber f) depth hlt
            have hrec := ih (Nat.pair (directTermNumber f) depth) hlt f depth rfl
            simp [liftChildValue, hchild, hread, hrec]
        have hx : liftChildValue (Nat.pair (directTermNumber (.app f x)) depth)
            (directTermNumber x) depth (liftHistory (Nat.pair (directTermNumber (.app f x)) depth)) =
            directTermNumber (liftFrom depth x) := by
          by_cases hchild : directTermNumber x ≤ depth
          · simp [liftChildValue, hchild, liftFrom_eq_self_of_code_le x depth hchild]
          · have hlt := directAppKey_right_lt f x depth
            have hread := liftHistoryRead_correct (Nat.pair (directTermNumber (.app f x)) depth)
              (directTermNumber x) depth hlt
            have hrec := ih (Nat.pair (directTermNumber x) depth) hlt x depth rfl
            simp [liftChildValue, hchild, hread, hrec]
        simp only [directTermNumber, Nat.succ_eq_add_one] at hf hx
        simp [liftValue, liftStepValue, directTag, directPayload, directAppNumber,
          directTermNumber, liftFrom, hcut', hf, hx]

#print axioms liftValue_correct
end LambdaTuring
