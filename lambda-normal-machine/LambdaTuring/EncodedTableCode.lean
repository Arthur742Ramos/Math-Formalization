/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.EncodedListLookup
public meta import LambdaTuring.EncodedListLookup
public import LambdaTuring.UniformMachineSyntax
public meta import LambdaTuring.UniformMachineSyntax

@[expose] public section

namespace LambdaTuring.Machine
open Nat.Partrec
open LambdaTuring.EffectiveCode

def addPairCode : Code := .prec Code.id (.comp .succ (.comp .right .right))

theorem addPairCode_eval (a n : Nat) :
    addPairCode.eval (Nat.pair a n) = Part.some (a + n) := by
  induction n with
  | zero =>
    rw [addPairCode, Code.eval_prec_zero]
    simp
  | succ n ih =>
    rw [addPairCode, Code.eval_prec_succ]
    change (Code.eval addPairCode (Nat.pair a n)).bind _ = _
    rw [ih]
    change (Part.some (a + n)).bind
      (fun z => Code.eval (.comp .succ (.comp .right .right))
        (Nat.pair a (Nat.pair n z))) = _
    rw [Part.bind_some]
    have hproj : Code.eval (.comp .right .right) (Nat.pair a (Nat.pair n (a + n))) =
        Part.some (a + n) := by
      change (Code.eval .right _).bind (fun z => Code.eval .right z) = _
      simp [Code.eval, Part.bind_some]
    have hs : Code.eval .succ (a + n) = Part.some (Nat.succ (a + n)) := rfl
    have h := evalCompSome .succ (.comp .right .right) _ _ _ hproj hs
    simpa [Nat.add_assoc] using h

def doubleCode : Code := .comp addPairCode (.pair Code.id Code.id)
def tripleCode : Code := .comp addPairCode (.pair doubleCode Code.id)

theorem doubleCode_eval (n : Nat) : doubleCode.eval n = Part.some (n + n) := by
  have hp := evalPairSome Code.id Code.id n n n (Code.eval_id n) (Code.eval_id n)
  exact evalCompSome addPairCode _ _ _ _ hp (addPairCode_eval n n)

theorem tripleCode_eval (n : Nat) : tripleCode.eval n = Part.some (n * 3) := by
  have hp := evalPairSome doubleCode Code.id n (n + n) n (doubleCode_eval n) (Code.eval_id n)
  have h := evalCompSome addPairCode _ _ _ _ hp (addPairCode_eval (n + n) n)
  simpa [tripleCode, Nat.mul_succ, Nat.mul_zero, Nat.add_assoc] using h

def tableIndexCode : Code := .comp addPairCode (.pair (.comp tripleCode .left) .right)

theorem tableIndexCode_eval (q : Nat) (s : Symbol) :
    tableIndexCode.eval (Nat.pair q (Encodable.encode s)) =
      Part.some (q * 3 + symbolIndex s) := by
  let input := Nat.pair q (Encodable.encode s)
  have hl : Code.eval .left input = Part.some q := by simp [input, Code.eval]
  have hr : Code.eval .right input = Part.some (Encodable.encode s) := by simp [input, Code.eval]
  have ht := evalCompSome tripleCode .left _ _ _ hl (tripleCode_eval q)
  have hp := evalPairSome (.comp tripleCode .left) .right _ _ _ ht hr
  have h := evalCompSome addPairCode _ _ _ _ hp (addPairCode_eval (q * 3) (Encodable.encode s))
  simpa [tableIndexCode, input, symbol_encoded] using h

def tableInstructionCode : Code :=
  .comp listLookupFlattenCode (.pair .left (.comp tableIndexCode .right))

theorem tableInstructionCode_eval (p : RawTable) (q : Nat) (s : Symbol) :
    tableInstructionCode.eval (Nat.pair (Encodable.encode p) (Nat.pair q (Encodable.encode s))) =
      Part.some (Encodable.encode (rawInstruction p q s)) := by
  let input := Nat.pair (Encodable.encode p) (Nat.pair q (Encodable.encode s))
  have hp : Code.eval .left input = Part.some (Encodable.encode p) := by simp [input, Code.eval]
  have hs : Code.eval .right input = Part.some (Nat.pair q (Encodable.encode s)) := by
    simp [input, Code.eval]
  have hi := evalCompSome tableIndexCode .right _ _ _ hs (tableIndexCode_eval q s)
  have hpair := evalPairSome .left (.comp tableIndexCode .right) _ _ _ hp hi
  have h := evalCompSome listLookupFlattenCode _ _ _ _ hpair
    (listLookupFlattenCode_eval p (q * 3 + symbolIndex s))
  simpa [tableInstructionCode, rawInstruction, input] using h

#print axioms addPairCode
#print axioms tableInstructionCode
#print axioms tableInstructionCode_eval
end LambdaTuring.Machine
