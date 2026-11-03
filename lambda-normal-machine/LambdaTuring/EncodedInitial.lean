/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.EncodedUnaryCount
public meta import LambdaTuring.EncodedUnaryCount

@[expose] public section

namespace LambdaTuring.Machine
open Nat.Partrec
open LambdaTuring.EffectiveCode

def replicateOneStepCode : Code :=
  .comp listConsCode (.pair (Code.const 1) (.comp .right .right))
def replicateOneFoldCode : Code := .prec .zero replicateOneStepCode
def replicateOneCode : Code := .comp replicateOneFoldCode (.pair .zero Code.id)

theorem replicateOneFoldCode_eval (a n : Nat) :
    replicateOneFoldCode.eval (Nat.pair a n) = Part.some (Encodable.encode (List.replicate n Symbol.one)) := by
  induction n with
  | zero => rw [replicateOneFoldCode, Code.eval_prec_zero]; rfl
  | succ n ih =>
    rw [replicateOneFoldCode, Code.eval_prec_succ]
    change (Code.eval replicateOneFoldCode (Nat.pair a n)).bind _ = _
    rw [ih]
    change (Part.some (Encodable.encode (List.replicate n Symbol.one))).bind
      (fun z => replicateOneStepCode.eval (Nat.pair a (Nat.pair n z))) = _
    rw [Part.bind_some]
    have hc : (Code.const 1).eval (Nat.pair a (Nat.pair n (Encodable.encode (List.replicate n Symbol.one)))) =
        Part.some 1 := Code.eval_const 1 _
    have ht : Code.eval (.comp .right .right)
        (Nat.pair a (Nat.pair n (Encodable.encode (List.replicate n Symbol.one)))) =
          Part.some (Encodable.encode (List.replicate n Symbol.one)) := by
      change (Code.eval .right _).bind (fun z => Code.eval .right z) = _
      simp [Code.eval, Part.bind_some]
    have hpair := evalPairSome (Code.const 1) (.comp .right .right) _ _ _ hc ht
    have h := evalCompSome listConsCode _ _ _ _ hpair (listCons_encoded Symbol.one (List.replicate n Symbol.one))
    simpa [replicateOneStepCode, List.replicate_succ, symbol_encoded, symbolIndex] using h

theorem replicateOneCode_eval (n : Nat) :
    replicateOneCode.eval n = Part.some (Encodable.encode (List.replicate n Symbol.one)) := by
  have hz : Code.eval .zero n = Part.some 0 := rfl
  have hp := evalPairSome .zero Code.id n 0 n hz (Code.eval_id n)
  exact evalCompSome replicateOneFoldCode _ _ _ _ hp (replicateOneFoldCode_eval 0 n)

def initialRawCode : Code :=
  .pair .zero (.pair .zero (.pair (Code.const 1) replicateOneCode))

theorem initialRawCode_eval (n : Nat) :
    initialRawCode.eval n = Part.some (Encodable.encode ((0, ⟨[], .one, List.replicate n .one⟩) : RawConfig)) := by
  have hz : Code.eval .zero n = Part.some 0 := rfl
  have ho : (Code.const 1).eval n = Part.some 1 := Code.eval_const 1 n
  have htail := replicateOneCode_eval n
  have h := evalPairSome .zero _ n 0 _ hz
    (evalPairSome .zero _ n 0 _ hz (evalPairSome (Code.const 1) replicateOneCode n 1 _ ho htail))
  simpa [initialRawCode, tape_encoded, Encodable.encode_prod_val, symbol_encoded, symbolIndex] using h

#print axioms replicateOneCode
#print axioms initialRawCode
#print axioms initialRawCode_eval
end LambdaTuring.Machine
