/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.EncodedTableCode
public meta import LambdaTuring.EncodedTableCode

@[expose] public section

namespace LambdaTuring.Machine
open Nat.Partrec
open LambdaTuring.EffectiveCode

def stepTableCode : Code := .left
def stepConfigCode : Code := .right
def stepStateCode : Code := .comp .left stepConfigCode
def stepTapeCode : Code := .comp .right stepConfigCode
def stepSymbolCode : Code := .comp tapeHeadCode stepTapeCode
def stepInstructionInputCode : Code := .pair stepTableCode (.pair stepStateCode stepSymbolCode)
def stepInstructionCode : Code := .comp tableInstructionCode stepInstructionInputCode
def stepRawInstructionCode : Code := .comp predCode stepInstructionCode
def stepNextStateCode : Code := .comp .left stepRawInstructionCode
def stepActionCode : Code := .comp .right stepRawInstructionCode
def stepNewTapeCode : Code := .comp performCode (.pair stepActionCode stepTapeCode)
def stepSomeResultCode : Code := .comp .succ (.pair stepNextStateCode stepNewTapeCode)
def rawStepCode : Code := chooseZeroCode stepInstructionCode .zero stepSomeResultCode

theorem instructionCode_pred (i : Option (Nat × Action)) :
    (Encodable.encode i).pred = Encodable.encode (i.getD (0, .left)) := by
  cases i with
  | none => rfl
  | some p => rfl

theorem rawStepCode_eval (p : RawTable) (c : RawConfig) :
    rawStepCode.eval (Nat.pair (Encodable.encode p) (Encodable.encode c)) =
      Part.some (Encodable.encode (rawStep p c)) := by
  let input := Nat.pair (Encodable.encode p) (Encodable.encode c)
  let instr := rawInstruction p c.1 c.2.head
  let fallback := instr.getD (0, Action.left)
  have hp : stepTableCode.eval input = Part.some (Encodable.encode p) := by
    simp [input, stepTableCode, Code.eval]
  have hc : stepConfigCode.eval input = Part.some (Encodable.encode c) := by
    simp [input, stepConfigCode, Code.eval]
  have hcstate : Code.eval .left (Encodable.encode c) = Part.some c.1 := by
    rcases c with ⟨q, t⟩
    simp [Code.eval, Encodable.encode_prod_val]
  have hctape : Code.eval .right (Encodable.encode c) = Part.some (Encodable.encode c.2) := by
    rcases c with ⟨q, t⟩
    simp [Code.eval, Encodable.encode_prod_val]
  have hstate := evalCompSome .left stepConfigCode _ _ _ hc hcstate
  have htape := evalCompSome .right stepConfigCode _ _ _ hc hctape
  have hsymbol := evalCompSome tapeHeadCode stepTapeCode _ _ _ htape (tapeHeadCode_eval c.2)
  have hs := evalPairSome stepStateCode stepSymbolCode _ _ _ hstate hsymbol
  have hiInput := evalPairSome stepTableCode (.pair stepStateCode stepSymbolCode) _ _ _ hp hs
  have hi := evalCompSome tableInstructionCode stepInstructionInputCode _ _ _ hiInput
    (tableInstructionCode_eval p c.1 c.2.head)
  have hraw := evalCompSome predCode stepInstructionCode _ _ _ hi (eval_predCode (Encodable.encode instr))
  rw [instructionCode_pred] at hraw
  have hfstate : Code.eval .left (Encodable.encode fallback) = Part.some fallback.1 := by
    rcases fallback with ⟨q, a⟩
    simp [Code.eval, Encodable.encode_prod_val]
  have hfaction : Code.eval .right (Encodable.encode fallback) = Part.some (Encodable.encode fallback.2) := by
    rcases fallback with ⟨q, a⟩
    simp [Code.eval, Encodable.encode_prod_val]
  have hn := evalCompSome .left stepRawInstructionCode _ _ _ hraw hfstate
  have ha := evalCompSome .right stepRawInstructionCode _ _ _ hraw hfaction
  have hat := evalPairSome stepActionCode stepTapeCode _ _ _ ha htape
  have hnew := evalCompSome performCode (.pair stepActionCode stepTapeCode) _ _ _ hat
    (performCode_eval fallback.2 c.2)
  have hconfig := evalPairSome stepNextStateCode stepNewTapeCode _ _ _ hn hnew
  have hsucceed := evalCompSome .succ (.pair stepNextStateCode stepNewTapeCode) _ _ _ hconfig
    (show Code.eval .succ _ = Part.some _ from rfl)
  have hzero : Code.eval .zero input = Part.some 0 := rfl
  have hresult := chooseZeroCode_eval stepInstructionCode .zero stepSomeResultCode _ _ _ _ hi hzero hsucceed
  cases he : instr with
  | none =>
    simpa [rawStepCode, rawStep, input, instr, he] using hresult
  | some qa =>
    rcases qa with ⟨q, a⟩
    simpa [rawStepCode, rawStep, input, instr, fallback, he, Encodable.encode_prod_val] using hresult

theorem publicStepCode_eval {states : Nat} (p : Program states) (c : Config states) :
    rawStepCode.eval (Nat.pair (Encodable.encode (eraseProgram p)) (Encodable.encode (eraseConfig c))) =
      Part.some (Encodable.encode ((step p c).map eraseConfig)) := by
  rw [rawStepCode_eval, rawStep_erase]

#print axioms rawStepCode
#print axioms rawStepCode_eval
#print axioms publicStepCode_eval
end LambdaTuring.Machine
