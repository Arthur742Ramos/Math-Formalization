/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectBetaReference
public meta import LambdaTuring.DirectBetaReference

@[expose] public section

namespace LambdaTuring
open Nat.Partrec
open LambdaTuring.Machine
open LambdaTuring.EffectiveCode

def betaZeroRep : LiftStepRep (fun _ _ => 0) := ⟨.zero, fun _ _ _ => rfl⟩

def betaEqualRep {f g : Nat → List Nat → Nat} (rf : LiftStepRep f) (rg : LiftStepRep g) :
    LiftStepRep (fun k h => if f k h = g k h then 1 else 0) := by
  refine ⟨.comp equalNatCode (.pair rf.code rg.code), ?_⟩
  intro context key history
  have hp := evalPairSome rf.code rg.code _ _ _ (rf.sound context key history) (rg.sound context key history)
  exact evalCompSome equalNatCode _ _ _ _ hp (equalNatCode_eval (f key history) (g key history))

def betaSubstRep {f g : Nat → List Nat → Nat} (rf : LiftStepRep f) (rg : LiftStepRep g) :
    LiftStepRep (fun k h => substValue (f k h) (g k h)) := by
  refine ⟨.comp directSubstCode (.pair rf.code rg.code), ?_⟩
  intro context key history
  have hp := evalPairSome rf.code rg.code _ _ _ (rf.sound context key history) (rg.sound context key history)
  exact evalCompSome directSubstCode _ _ _ _ hp (directSubstCode_any (f key history) (g key history))

def betaOneRep := liftSuccRep betaZeroRep
def betaTwoRep := liftSuccRep betaOneRep
def betaDirectionRep := liftLeftRep (liftPredRep liftDepthRep)
def betaRestRep := liftRightRep (liftPredRep liftDepthRep)
def betaFunctionRep := liftLeftChildRep
def betaArgumentRep := liftRightChildRep
def betaFunctionTagRep := liftLeftRep (liftPredRep betaFunctionRep)
def betaFunctionBodyRep := liftRightRep (liftPredRep betaFunctionRep)
def betaReadRep {f : Nat → List Nat → Nat} (child : LiftStepRep f) :=
  LiftStepRep.lookup liftKeyRep (child.pair betaRestRep)
def betaWrapAbsRep {f : Nat → List Nat → Nat} (r : LiftStepRep f) :=
  r.select betaZeroRep (liftSuccRep (liftAbsRep (liftPredRep r)))
def betaWrapLeftRep {f g : Nat → List Nat → Nat} (r : LiftStepRep f) (arg : LiftStepRep g) :=
  r.select betaZeroRep (liftSuccRep (liftAppRep (liftPredRep r) arg))
def betaWrapRightRep {f g : Nat → List Nat → Nat} (arg : LiftStepRep f) (r : LiftStepRep g) :=
  r.select betaZeroRep (liftSuccRep (liftAppRep arg (liftPredRep r)))

def betaRootRep := (betaEqualRep liftTagRep betaTwoRep).select betaZeroRep
  ((betaEqualRep betaFunctionTagRep betaOneRep).select betaZeroRep
    (liftSuccRep (betaSubstRep betaArgumentRep (betaFunctionBodyRep.pair betaZeroRep))))
def betaAbsDispatchRep := betaDirectionRep.select (betaWrapAbsRep (betaReadRep liftPayloadRep)) betaZeroRep
def betaAppDispatchRep := betaDirectionRep.select (betaWrapLeftRep (betaReadRep liftLeftChildRep) liftRightChildRep)
  ((betaEqualRep betaDirectionRep betaOneRep).select betaZeroRep
    (betaWrapRightRep liftLeftChildRep (betaReadRep liftRightChildRep)))
def betaPathStepRep := liftDepthRep.select betaRootRep
  ((betaEqualRep liftTagRep betaOneRep).select
    ((betaEqualRep liftTagRep betaTwoRep).select betaZeroRep betaAppDispatchRep)
    betaAbsDispatchRep)

def betaEqCode (a b : Code) : Code := .comp equalNatCode (.pair a b)
def betaReadCode (child : Code) : Code := .comp historyLookupCode
  (.pair (.pair liftKeyCode (.pair child (.comp .right (.comp predCode liftDepthCode)))) liftHistoryCode)
def betaWrapAbsCode (r : Code) : Code := chooseZeroCode r .zero
  (.comp .succ (.comp directAbsCode (.comp predCode r)))
def betaWrapLeftCode (r arg : Code) : Code := chooseZeroCode r .zero
  (.comp .succ (.comp directAppCode (.pair (.comp predCode r) arg)))
def betaWrapRightCode (arg r : Code) : Code := chooseZeroCode r .zero
  (.comp .succ (.comp directAppCode (.pair arg (.comp predCode r))))
def betaFunctionCode : Code := .comp .left liftPayloadCode
def betaArgumentCode : Code := .comp .right liftPayloadCode
def betaDirectionCode : Code := .comp .left (.comp predCode liftDepthCode)
def betaRootCode : Code := chooseZeroCode (betaEqCode liftTagCode (.comp .succ (.comp .succ .zero))) .zero
  (chooseZeroCode (betaEqCode (.comp .left (.comp predCode betaFunctionCode)) (.comp .succ .zero)) .zero
    (.comp .succ (.comp directSubstCode
      (.pair betaArgumentCode (.pair (.comp .right (.comp predCode betaFunctionCode)) .zero)))))
def betaAbsDispatchCode : Code := chooseZeroCode betaDirectionCode (betaWrapAbsCode (betaReadCode liftPayloadCode)) .zero
def betaAppDispatchCode : Code := chooseZeroCode betaDirectionCode
  (betaWrapLeftCode (betaReadCode betaFunctionCode) betaArgumentCode)
  (chooseZeroCode (betaEqCode betaDirectionCode (.comp .succ .zero)) .zero
    (betaWrapRightCode betaFunctionCode (betaReadCode betaArgumentCode)))
def betaPathStepCode : Code := chooseZeroCode liftDepthCode betaRootCode
  (chooseZeroCode (betaEqCode liftTagCode (.comp .succ .zero))
    (chooseZeroCode (betaEqCode liftTagCode (.comp .succ (.comp .succ .zero))) .zero betaAppDispatchCode)
    betaAbsDispatchCode)

theorem betaPathStepRep_code : betaPathStepRep.code = betaPathStepCode := rfl

def betaPathStepFormula (key : Nat) (history : List Nat) : Nat :=
  let term := key.unpair.1
  let path := key.unpair.2
  let tag := directTag term
  let data := directPayload term
  let dir := path.pred.unpair.1
  let rest := path.pred.unpair.2
  let read := fun child => (history[key.pred - Nat.pair child rest]?).getD 0
  let wrapAbs := fun r => if r = 0 then 0 else (directAbsNumber r.pred) + 1
  let wrapLeft := fun r arg => if r = 0 then 0 else (directAppNumber r.pred arg) + 1
  let wrapRight := fun arg r => if r = 0 then 0 else (directAppNumber arg r.pred) + 1
  if path = 0 then
    if (if tag = 2 then 1 else 0) = 0 then 0
    else if (if directTag data.unpair.1 = 1 then 1 else 0) = 0 then 0
    else substValue data.unpair.2 (Nat.pair (directPayload data.unpair.1) 0) + 1
  else if (if tag = 1 then 1 else 0) = 0 then
    if (if tag = 2 then 1 else 0) = 0 then 0
    else if dir = 0 then wrapLeft (read data.unpair.1) data.unpair.2
    else if (if dir = 1 then 1 else 0) = 0 then 0 else wrapRight data.unpair.1 (read data.unpair.2)
  else if dir = 0 then wrapAbs (read data) else 0

theorem betaPathStepFormula_eq (key : Nat) (history : List Nat) :
    betaPathStepFormula key history = betaPathStepValue key history := by
  simp only [betaPathStepFormula, betaPathStepValue, betaRootValue, betaWrapAbs, betaWrapLeft,
    betaWrapRight, betaHistoryRead, Nat.pred_eq_sub_one]
  split_ifs <;> simp_all

theorem betaPathStepCode_eval (context key : Nat) (history : List Nat) :
    betaPathStepCode.eval (Nat.pair context (Nat.pair key (Encodable.encode history))) =
      Part.some (betaPathStepValue key history) := by
  have h := betaPathStepRep.sound context key history
  rw [betaPathStepRep_code] at h
  change betaPathStepCode.eval (Nat.pair context (Nat.pair key (Encodable.encode history))) =
      Part.some (betaPathStepFormula key history) at h
  rw [betaPathStepFormula_eq] at h
  exact h

def betaAtPathCode : Code := .comp (courseCode betaPathStepCode) (.pair .zero Code.id)

theorem betaAtPathCode_any (term path : Nat) :
    betaAtPathCode.eval (Nat.pair term path) = Part.some (betaPathValue (Nat.pair term path)) := by
  have hstep : ∀ context key,
      betaPathStepCode.eval (Nat.pair context
        (Nat.pair key (Encodable.encode (courseHistory (fun _ k => betaPathValue k) context key)))) =
          Part.some (betaPathValue key) := by
    intro context key
    rw [betaPathHistory_eq_course, betaPathStepCode_eval]
    rfl
  let input := Nat.pair term path
  have hz : Code.eval .zero input = Part.some 0 := rfl
  have hp := evalPairSome .zero Code.id input 0 input hz (Code.eval_id input)
  have hcourse := courseCode_eval betaPathStepCode (fun _ key => betaPathValue key) hstep 0 input
  exact evalCompSome (courseCode betaPathStepCode) (.pair .zero Code.id) _ _ _ hp hcourse

theorem betaAtPathCode_eval (term : Term) (path : List Bool) :
    betaAtPathCode.eval (Nat.pair (directTermNumber term) (Encodable.encode path)) =
      Part.some (Encodable.encode ((betaAtPath path term).map directTermNumber)) := by
  rw [betaAtPathCode_any, betaPathValue_correct]

#print axioms betaPathStepCode
#print axioms betaAtPathCode
#print axioms betaAtPathCode_eval
end LambdaTuring
