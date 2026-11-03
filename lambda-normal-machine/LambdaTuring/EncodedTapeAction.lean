/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.EncodedTapeMove
public meta import LambdaTuring.EncodedTapeMove
public import LambdaTuring.NumericalCode
public meta import LambdaTuring.NumericalCode

@[expose] public section

namespace LambdaTuring.Machine
open Nat.Partrec
open LambdaTuring.EffectiveCode

/-- Select between two computations that are both known to produce values. -/
def chooseZeroCode (test yes no : Code) : Code :=
  .comp ifZeroCode (.pair (.pair yes no) test)

theorem chooseZeroCode_eval (test yes no : Code) (n q a b : Nat)
    (ht : test.eval n = Part.some q) (ha : yes.eval n = Part.some a)
    (hb : no.eval n = Part.some b) :
    (chooseZeroCode test yes no).eval n = Part.some (if q = 0 then a else b) := by
  have hvalues := evalPairSome yes no n a b ha hb
  have hinput := evalPairSome (.pair yes no) test n (Nat.pair a b) q hvalues ht
  exact evalCompSome ifZeroCode _ _ _ _ hinput (ifZeroCode_eval a b q)

def actionWriteSymbol : Action → Symbol
  | .left | .right => .blank
  | .write s => s

theorem actionEncoded_left : Encodable.encode Action.left = 0 := rfl
theorem actionEncoded_right : Encodable.encode Action.right = 1 := rfl
theorem actionEncoded_write (s : Symbol) :
    Encodable.encode (Action.write s) = Encodable.encode s + 2 := by
  cases s <;> rfl

theorem actionEncoded_predpred (a : Action) :
    (Encodable.encode a).pred.pred = Encodable.encode (actionWriteSymbol a) := by
  cases a with
  | left | right => rfl
  | write s => cases s <;> rfl

def actionTapeCode : Code := .right
def actionTagCode : Code := .left
def actionPredCode : Code := .comp predCode actionTagCode
def actionSymbolCode : Code := .comp predCode actionPredCode
def actionLeftCode : Code := .comp tapeMoveLeftCode actionTapeCode
def actionRightCode : Code := .comp tapeMoveRightCode actionTapeCode
def actionWriteCode : Code := .comp tapeWriteCode (.pair actionSymbolCode actionTapeCode)
def performCode : Code :=
  chooseZeroCode actionTagCode actionLeftCode
    (chooseZeroCode actionPredCode actionRightCode actionWriteCode)

theorem performCode_eval (a : Action) (t : Tape) :
    performCode.eval (Nat.pair (Encodable.encode a) (Encodable.encode t)) =
      Part.some (Encodable.encode (perform a t)) := by
  let input := Nat.pair (Encodable.encode a) (Encodable.encode t)
  have htag : actionTagCode.eval input = Part.some (Encodable.encode a) := by
    simp [input, actionTagCode, Code.eval]
  have htape : actionTapeCode.eval input = Part.some (Encodable.encode t) := by
    simp [input, actionTapeCode, Code.eval]
  have hpred := evalCompSome predCode actionTagCode _ _ _ htag (eval_predCode _)
  have hsymbol := evalCompSome predCode actionPredCode _ _ _ hpred (eval_predCode _)
  rw [actionEncoded_predpred] at hsymbol
  have hleft := evalCompSome tapeMoveLeftCode actionTapeCode _ _ _ htape (tapeMoveLeftCode_eval t)
  have hright := evalCompSome tapeMoveRightCode actionTapeCode _ _ _ htape (tapeMoveRightCode_eval t)
  have hwriteInput := evalPairSome actionSymbolCode actionTapeCode _ _ _ hsymbol htape
  have hwrite := evalCompSome tapeWriteCode (.pair actionSymbolCode actionTapeCode) _ _ _
    hwriteInput (tapeWriteCode_eval (actionWriteSymbol a) t)
  have hinner := chooseZeroCode_eval actionPredCode actionRightCode actionWriteCode _ _ _ _
    hpred hright hwrite
  have hresult := chooseZeroCode_eval actionTagCode actionLeftCode
    (chooseZeroCode actionPredCode actionRightCode actionWriteCode) _ _ _ _ htag hleft hinner
  cases a with
  | left => simpa [input, performCode, perform, actionEncoded_left] using hresult
  | right => simpa [input, performCode, perform, actionEncoded_right] using hresult
  | write s =>
    cases s <;> simpa [input, performCode, perform, actionWriteSymbol,
      actionEncoded_write, symbol_encoded, symbolIndex] using hresult

#print axioms performCode
#print axioms performCode_eval
end LambdaTuring.Machine
