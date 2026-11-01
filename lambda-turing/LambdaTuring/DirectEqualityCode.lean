/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectNumeralCode
public meta import LambdaTuring.DirectNumeralCode

@[expose] public section

namespace LambdaTuring
open Nat.Partrec
open LambdaTuring.Machine

def swapPairCode : Code := .pair .right .left
def reverseSubCode : Code := .comp subPairCode swapPairCode
def equalNatCode : Code := chooseZeroCode subPairCode
  (chooseZeroCode reverseSubCode (Code.const 1) .zero) .zero

theorem equalNatCode_eval (a b : Nat) :
    equalNatCode.eval (Nat.pair a b) = Part.some (if a = b then 1 else 0) := by
  let input := Nat.pair a b
  have hl : Code.eval .left input = Part.some a := by simp [input, Code.eval]
  have hr : Code.eval .right input = Part.some b := by simp [input, Code.eval]
  have hswap := evalPairSome .right .left _ _ _ hr hl
  have hreverse := evalCompSome subPairCode swapPairCode _ _ _ hswap (subPairCode_eval b a)
  have hsub := subPairCode_eval a b
  have hone := Code.eval_const 1 input
  have hz : Code.eval .zero input = Part.some 0 := rfl
  have hinner := chooseZeroCode_eval reverseSubCode (Code.const 1) .zero _ _ _ _ hreverse hone hz
  have h := chooseZeroCode_eval subPairCode
    (chooseZeroCode reverseSubCode (Code.const 1) .zero) .zero _ _ _ _ hsub hinner hz
  have heq : (if a - b = 0 then (if b - a = 0 then 1 else 0) else 0) =
      (if a = b then 1 else 0) := by
    split_ifs <;> omega
  simpa [equalNatCode, input, heq] using h

#print axioms equalNatCode
#print axioms equalNatCode_eval
end LambdaTuring
