/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ProofReifier
public meta import LambdaTuring.ProofReifier

@[expose] public section

namespace LambdaTuring.EffectiveCode
open Nat.Partrec

/-- Concrete syntax for encoded-pair addition, multiplication, and truncated subtraction. -/
def addWitness : TotalWitness (Nat.unpaired (· + ·)) := total_code_from% Nat.Primrec.add
def mulWitness : TotalWitness (Nat.unpaired (· * ·)) := total_code_from% Nat.Primrec.mul
def subWitness : TotalWitness (Nat.unpaired (· - ·)) := total_code_from% Nat.Primrec.sub

/-- Select between two already-defined numerical values using a zero test. -/
def ifZeroCode : Code := .prec .left (.comp .right .left)

theorem ifZeroCode_eval (x y n : Nat) :
    ifZeroCode.eval (Nat.pair (Nat.pair x y) n) =
      Part.some (if n = 0 then x else y) := by
  induction n with
  | zero =>
    rw [ifZeroCode, Code.eval_prec_zero]
    simp [Code.eval]
  | succ n ih =>
    rw [ifZeroCode, Code.eval_prec_succ]
    have hp : Code.eval (.prec .left (.comp .right .left)) (Nat.pair (Nat.pair x y) n) =
        Part.some (if n = 0 then x else y) := ih
    rw [hp]
    change (Part.some (if n = 0 then x else y)).bind
      (fun z => Code.eval (.comp .right .left) (Nat.pair (Nat.pair x y) (Nat.pair n z))) = _
    rw [Part.bind_some]
    change (Code.eval .left (Nat.pair (Nat.pair x y)
      (Nat.pair n (if n = 0 then x else y)))).bind (fun z => Code.eval .right z) = _
    have hl : Code.eval .left (Nat.pair (Nat.pair x y)
        (Nat.pair n (if n = 0 then x else y))) = Part.some (Nat.pair x y) := by
      simp [Code.eval]
    rw [hl, Part.bind_some]
    simp [Code.eval]

theorem addCode_eval (a b : Nat) :
    addWitness.code.eval (Nat.pair a b) = Part.some (a + b) := by
  simpa using addWitness.sound (Nat.pair a b)

theorem mulCode_eval (a b : Nat) :
    mulWitness.code.eval (Nat.pair a b) = Part.some (a * b) := by
  simpa using mulWitness.sound (Nat.pair a b)

theorem subCode_eval (a b : Nat) :
    subWitness.code.eval (Nat.pair a b) = Part.some (a - b) := by
  simpa using subWitness.sound (Nat.pair a b)

#eval mulWitness.code.evaln 10000 (Nat.pair 2 3)
#eval subWitness.code.evaln 10000 (Nat.pair 2 3)
#print axioms addCode_eval
#print axioms mulCode_eval
#print axioms subCode_eval
#print axioms ifZeroCode
#print axioms ifZeroCode_eval
end LambdaTuring.EffectiveCode
