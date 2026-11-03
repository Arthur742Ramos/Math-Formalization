/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.EncodedInitial
public meta import LambdaTuring.EncodedInitial

@[expose] public section

namespace LambdaTuring.Machine
open Nat.Partrec
open LambdaTuring.EffectiveCode

def postTableCode : Code := .left
def postResultCode : Code := .right
def postConfigCode : Code := .comp predCode postResultCode
def postTapeCode : Code := .comp .right postConfigCode
def postHeadCode : Code := .comp tapeHeadCode postTapeCode
def postRightCode : Code := .comp tapeRightCode postTapeCode
def postListCode : Code := .comp listConsCode (.pair postHeadCode postRightCode)
def postDecodeCode : Code := .comp decodeCode postListCode
def postStepCode : Code := .comp rawStepCode (.pair postTableCode postConfigCode)
def postHaltCode : Code := chooseZeroCode postStepCode postDecodeCode .zero
def postRunCode : Code := chooseZeroCode postResultCode .zero postHaltCode

theorem postRunCode_eval (p : RawTable) (r : Option RawConfig) :
    postRunCode.eval (Nat.pair (Encodable.encode p) (Encodable.encode r)) =
      Part.some (Encodable.encode (r.bind fun c =>
        if rawStep p c = Option.none then decode (c.2.head :: c.2.right) else Option.none)) := by
  let input := Nat.pair (Encodable.encode p) (Encodable.encode r)
  let c := r.getD emptyRawConfig
  have hp : postTableCode.eval input = Part.some (Encodable.encode p) := by simp [input, postTableCode, Code.eval]
  have hr : postResultCode.eval input = Part.some (Encodable.encode r) := by simp [input, postResultCode, Code.eval]
  have hc := evalCompSome predCode postResultCode _ _ _ hr (eval_predCode (Encodable.encode r))
  rw [optionalConfig_pred] at hc
  have hctape : Code.eval .right (Encodable.encode c) = Part.some (Encodable.encode c.2) := by
    rcases c with ⟨q, t⟩
    simp [Code.eval, Encodable.encode_prod_val]
  have ht := evalCompSome .right postConfigCode _ _ _ hc hctape
  have hh := evalCompSome tapeHeadCode postTapeCode _ _ _ ht (tapeHeadCode_eval c.2)
  have hright := evalCompSome tapeRightCode postTapeCode _ _ _ ht (tapeRightCode_eval c.2)
  have hlistPair := evalPairSome postHeadCode postRightCode _ _ _ hh hright
  have hlist := evalCompSome listConsCode _ _ _ _ hlistPair (listCons_encoded c.2.head c.2.right)
  have hdecode := evalCompSome decodeCode postListCode _ _ _ hlist (decodeCode_eval (c.2.head :: c.2.right))
  have hstepPair := evalPairSome postTableCode postConfigCode _ _ _ hp hc
  have hstep := evalCompSome rawStepCode _ _ _ _ hstepPair (rawStepCode_eval p c)
  have hz : Code.eval .zero input = Part.some 0 := rfl
  have hhalt := chooseZeroCode_eval postStepCode postDecodeCode .zero _ _ _ _ hstep hdecode hz
  have hresult := chooseZeroCode_eval postResultCode .zero postHaltCode _ _ _ _ hr hz hhalt
  cases r with
  | none => simpa [postRunCode, input] using hresult
  | some cfg =>
    dsimp [c] at hresult
    cases hs : rawStep p cfg with
    | none => simpa [postRunCode, input, hs] using hresult
    | some d => simpa [postRunCode, input, hs] using hresult

#print axioms postRunCode
#print axioms postRunCode_eval
end LambdaTuring.Machine
