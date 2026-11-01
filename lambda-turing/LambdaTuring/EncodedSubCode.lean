/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.EncodedMachineRun
public meta import LambdaTuring.EncodedMachineRun

@[expose] public section

namespace LambdaTuring.Machine
open Nat.Partrec
open LambdaTuring.EffectiveCode

def subPairCode : Code := .prec Code.id (.comp predCode (.comp .right .right))

theorem subPairCode_eval (a n : Nat) :
    subPairCode.eval (Nat.pair a n) = Part.some (a - n) := by
  induction n with
  | zero =>
    rw [subPairCode, Code.eval_prec_zero]
    simp
  | succ n ih =>
    rw [subPairCode, Code.eval_prec_succ]
    change (Code.eval subPairCode (Nat.pair a n)).bind _ = _
    rw [ih]
    change (Part.some (a - n)).bind
      (fun z => Code.eval (.comp predCode (.comp .right .right))
        (Nat.pair a (Nat.pair n z))) = _
    rw [Part.bind_some]
    have hproj : Code.eval (.comp .right .right) (Nat.pair a (Nat.pair n (a - n))) =
        Part.some (a - n) := by
      change (Code.eval .right _).bind (fun z => Code.eval .right z) = _
      simp [Code.eval, Part.bind_some]
    have h := evalCompSome predCode (.comp .right .right) _ _ _ hproj (eval_predCode (a - n))
    rw [Nat.sub_succ]
    exact h

#print axioms subPairCode
#print axioms subPairCode_eval
end LambdaTuring.Machine
