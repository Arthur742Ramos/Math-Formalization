/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectTermCode
public meta import LambdaTuring.DirectTermCode

@[expose] public section

namespace LambdaTuring
open Nat.Partrec
open LambdaTuring.Machine

def directBodyStepCode : Code :=
  .comp directAppCode (.pair (Code.const (directTermNumber (.var 1))) (.comp .right .right))
def directBodyFoldCode : Code := .prec (Code.const (directTermNumber (.var 0))) directBodyStepCode
def directBodyCode : Code := .comp directBodyFoldCode (.pair .zero Code.id)
def directChurchCode : Code := .comp directAbsCode (.comp directAbsCode directBodyCode)
def directNumeralApplicationCode : Code := .comp directAppCode (.pair .left (.comp directChurchCode .right))

theorem directBodyFoldCode_eval (a n : Nat) :
    directBodyFoldCode.eval (Nat.pair a n) = Part.some (directTermNumber (churchBody n)) := by
  induction n with
  | zero =>
    rw [directBodyFoldCode, Code.eval_prec_zero]
    exact Code.eval_const (directTermNumber (.var 0)) a
  | succ n ih =>
    rw [directBodyFoldCode, Code.eval_prec_succ]
    change (Code.eval directBodyFoldCode (Nat.pair a n)).bind _ = _
    rw [ih]
    change (Part.some (directTermNumber (churchBody n))).bind
      (fun z => directBodyStepCode.eval (Nat.pair a (Nat.pair n z))) = _
    rw [Part.bind_some]
    have hc := Code.eval_const (directTermNumber (.var 1))
      (Nat.pair a (Nat.pair n (directTermNumber (churchBody n))))
    have hp : Code.eval (.comp .right .right)
        (Nat.pair a (Nat.pair n (directTermNumber (churchBody n)))) =
        Part.some (directTermNumber (churchBody n)) := by
      change (Code.eval .right _).bind (fun x => Code.eval .right x) = _
      simp [Code.eval, Part.bind_some]
    have hpair := evalPairSome (Code.const (directTermNumber (.var 1))) (.comp .right .right) _ _ _ hc hp
    have h := evalCompSome directAppCode _ _ _ _ hpair (directAppCode_eval (.var 1) (churchBody n))
    exact h

theorem directBodyCode_eval (n : Nat) :
    directBodyCode.eval n = Part.some (directTermNumber (churchBody n)) := by
  have hz : Code.eval .zero n = Part.some 0 := rfl
  have hp := evalPairSome .zero Code.id n 0 n hz (Code.eval_id n)
  exact evalCompSome directBodyFoldCode _ _ _ _ hp (directBodyFoldCode_eval 0 n)

theorem directChurchCode_eval (n : Nat) :
    directChurchCode.eval n = Part.some (directTermNumber (church n)) := by
  have inner := evalCompSome directAbsCode directBodyCode _ _ _ (directBodyCode_eval n)
    (directAbsCode_eval (churchBody n))
  have outer := evalCompSome directAbsCode (.comp directAbsCode directBodyCode) _ _ _ inner
    (directAbsCode_eval (.abs (churchBody n)))
  exact outer

theorem directNumeralApplicationCode_eval (t : Term) (n : Nat) :
    directNumeralApplicationCode.eval (Nat.pair (directTermNumber t) n) =
      Part.some (directTermNumber (.app t (church n))) := by
  let input := Nat.pair (directTermNumber t) n
  have hl : Code.eval .left input = Part.some (directTermNumber t) := by simp [input, Code.eval]
  have hr : Code.eval .right input = Part.some n := by simp [input, Code.eval]
  have hc := evalCompSome directChurchCode .right _ _ _ hr (directChurchCode_eval n)
  have hp := evalPairSome .left (.comp directChurchCode .right) _ _ _ hl hc
  exact evalCompSome directAppCode _ _ _ _ hp (directAppCode_eval t (church n))

#print axioms directChurchCode
#print axioms directNumeralApplicationCode
#print axioms directNumeralApplicationCode_eval
end LambdaTuring
