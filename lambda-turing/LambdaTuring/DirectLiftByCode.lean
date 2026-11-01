/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectLiftCode
public meta import LambdaTuring.DirectLiftCode

@[expose] public section

namespace LambdaTuring
open Nat.Partrec
open LambdaTuring.Machine

def liftByValue : Nat → Nat → Nat
  | 0, value => value
  | n + 1, value => liftValue (Nat.pair (liftByValue n value) 0)

theorem liftByValue_correct (t : Term) (n : Nat) :
    liftByValue n (directTermNumber t) = directTermNumber (liftBy n t) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [liftByValue, liftBy, ih, liftValue_correct]

def directLiftZeroCode : Code := .comp directLiftCode (.pair Code.id .zero)
def directLiftByStepCode : Code := .comp directLiftZeroCode (.comp .right .right)
def directLiftByCode : Code := .prec Code.id directLiftByStepCode

theorem directLiftZeroCode_eval (t : Term) :
    directLiftZeroCode.eval (directTermNumber t) = Part.some (directTermNumber (liftFrom 0 t)) := by
  have hz : Code.eval .zero (directTermNumber t) = Part.some 0 := rfl
  have hp := evalPairSome Code.id .zero _ _ _ (Code.eval_id (directTermNumber t)) hz
  exact evalCompSome directLiftCode _ _ _ _ hp (directLiftCode_eval t 0)

theorem directLiftZeroCode_any (value : Nat) :
    directLiftZeroCode.eval value = Part.some (liftValue (Nat.pair value 0)) := by
  have hz : Code.eval .zero value = Part.some 0 := rfl
  have hp := evalPairSome Code.id .zero _ _ _ (Code.eval_id value) hz
  exact evalCompSome directLiftCode _ _ _ _ hp (directLiftCode_any value 0)

theorem directLiftByCode_any (value n : Nat) :
    directLiftByCode.eval (Nat.pair value n) = Part.some (liftByValue n value) := by
  induction n with
  | zero => rw [directLiftByCode, Code.eval_prec_zero]; simp [liftByValue]
  | succ n ih =>
    rw [directLiftByCode, Code.eval_prec_succ]
    change (directLiftByCode.eval (Nat.pair value n)).bind _ = _
    rw [ih]
    change (Part.some (liftByValue n value)).bind
      (fun z => directLiftByStepCode.eval (Nat.pair value (Nat.pair n z))) = _
    rw [Part.bind_some]
    have hproj : Code.eval (.comp .right .right)
        (Nat.pair value (Nat.pair n (liftByValue n value))) =
        Part.some (liftByValue n value) := by
      change (Code.eval .right _).bind (fun z => Code.eval .right z) = _
      simp [Code.eval, Part.bind_some]
    have h := evalCompSome directLiftZeroCode (.comp .right .right) _ _ _ hproj
      (directLiftZeroCode_any (liftByValue n value))
    exact h

theorem directLiftByCode_eval (t : Term) (n : Nat) :
    directLiftByCode.eval (Nat.pair (directTermNumber t) n) = Part.some (directTermNumber (liftBy n t)) := by
  rw [directLiftByCode_any, liftByValue_correct]

#print axioms directLiftByCode
#print axioms directLiftByCode_eval
end LambdaTuring
