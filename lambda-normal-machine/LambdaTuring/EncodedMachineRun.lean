/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.EncodedMachineStep
public meta import LambdaTuring.EncodedMachineStep

@[expose] public section

namespace LambdaTuring.Machine
open Nat.Partrec
open LambdaTuring.EffectiveCode

def emptyRawConfig : RawConfig := (0, ⟨[], .blank, []⟩)

theorem emptyRawConfig_encoded : Encodable.encode emptyRawConfig = 0 := rfl

theorem optionalConfig_pred (r : Option RawConfig) :
    (Encodable.encode r).pred = Encodable.encode (r.getD emptyRawConfig) := by
  cases r with
  | none => rfl
  | some c => rfl

def runBaseCode : Code := .comp .succ .right
def runTableCode : Code := .comp .left .left
def runPriorCode : Code := .comp .right .right
def runConfigCode : Code := .comp predCode runPriorCode
def runApplyCode : Code := .comp rawStepCode (.pair runTableCode runConfigCode)
def runStepCode : Code := chooseZeroCode runPriorCode .zero runApplyCode
def rawRunCode : Code := .prec runBaseCode runStepCode

theorem runStepCode_eval (p : RawTable) (start : RawConfig) (fuel : Nat) (prior : Option RawConfig) :
    runStepCode.eval (Nat.pair (Nat.pair (Encodable.encode p) (Encodable.encode start))
        (Nat.pair fuel (Encodable.encode prior))) =
      Part.some (Encodable.encode (prior.bind (rawStep p))) := by
  let context := Nat.pair (Encodable.encode p) (Encodable.encode start)
  let input := Nat.pair context (Nat.pair fuel (Encodable.encode prior))
  have hcontext : Code.eval .left input = Part.some context := by simp [input, Code.eval]
  have htable : Code.eval .left context = Part.some (Encodable.encode p) := by simp [context, Code.eval]
  have hp := evalCompSome .left .left _ _ _ hcontext htable
  have hrest : Code.eval .right input = Part.some (Nat.pair fuel (Encodable.encode prior)) := by
    simp [input, Code.eval]
  have hprior : Code.eval .right (Nat.pair fuel (Encodable.encode prior)) =
      Part.some (Encodable.encode prior) := by simp [Code.eval]
  have hpriorPair := evalCompSome .right .right _ _ _ hrest hprior
  have hcode : runPriorCode.eval input = Part.some (Encodable.encode prior) := by
    exact hpriorPair
  have hconfig := evalCompSome predCode runPriorCode _ _ _ hcode (eval_predCode (Encodable.encode prior))
  rw [optionalConfig_pred] at hconfig
  have hpconfig := evalPairSome runTableCode runConfigCode _ _ _ hp hconfig
  have hnext := evalCompSome rawStepCode (.pair runTableCode runConfigCode) _ _ _ hpconfig
    (rawStepCode_eval p (prior.getD emptyRawConfig))
  have hzero : Code.eval .zero input = Part.some 0 := rfl
  have hresult := chooseZeroCode_eval runPriorCode .zero runApplyCode _ _ _ _ hcode hzero hnext
  cases prior with
  | none => simpa [runStepCode, input, context] using hresult
  | some c => simpa [runStepCode, input, context] using hresult

theorem rawRunCode_eval (p : RawTable) (start : RawConfig) (fuel : Nat) :
    rawRunCode.eval (Nat.pair (Nat.pair (Encodable.encode p) (Encodable.encode start)) fuel) =
      Part.some (Encodable.encode (rawRunExact p fuel start)) := by
  induction fuel with
  | zero =>
    rw [rawRunCode, Code.eval_prec_zero]
    change (Code.eval .right (Nat.pair (Encodable.encode p) (Encodable.encode start))).bind
      (fun x => Code.eval .succ x) = _
    simp [Code.eval, Part.bind_some, rawRunExact]
  | succ fuel ih =>
    rw [rawRunCode, Code.eval_prec_succ]
    change (Code.eval rawRunCode (Nat.pair (Nat.pair (Encodable.encode p) (Encodable.encode start)) fuel)).bind _ = _
    rw [ih]
    change (Part.some (Encodable.encode (rawRunExact p fuel start))).bind
      (fun z => runStepCode.eval (Nat.pair (Nat.pair (Encodable.encode p) (Encodable.encode start))
        (Nat.pair fuel z))) = _
    rw [Part.bind_some, runStepCode_eval]
    rfl

theorem publicRunCode_eval {states : Nat} (p : Program states) (start : Config states) (fuel : Nat) :
    rawRunCode.eval (Nat.pair
      (Nat.pair (Encodable.encode (eraseProgram p)) (Encodable.encode (eraseConfig start))) fuel) =
      Part.some (Encodable.encode ((runExact p fuel start).map eraseConfig)) := by
  rw [rawRunCode_eval, rawRunExact_erase]

#print axioms rawRunCode
#print axioms rawRunCode_eval
#print axioms publicRunCode_eval
end LambdaTuring.Machine
