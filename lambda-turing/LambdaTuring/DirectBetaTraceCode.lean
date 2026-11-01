/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectBetaCertificates
public meta import LambdaTuring.DirectBetaCertificates

@[expose] public section

namespace LambdaTuring
open Nat.Partrec
open LambdaTuring.Machine
open LambdaTuring.EffectiveCode

def betaTraceHeadCode : Code := .comp .left (.comp predCode .right)
def betaTraceTailCode : Code := .comp .right (.comp predCode .right)
def betaTraceApplyCode : Code := .comp betaAtPathCode
  (.pair (.comp predCode .left) betaTraceHeadCode)
def betaTraceNextCode : Code := chooseZeroCode .left .zero betaTraceApplyCode
def betaTraceTickCode : Code := chooseZeroCode .right Code.id
  (.pair betaTraceNextCode betaTraceTailCode)
def betaTraceIterCode : Code := .prec Code.id (.comp betaTraceTickCode (.comp .right .right))

def betaTraceTickValue (state : Nat) : Nat :=
  let current := state.unpair.1
  let paths := state.unpair.2
  if paths = 0 then state
  else Nat.pair (if current = 0 then 0 else
    betaPathValue (Nat.pair current.pred paths.pred.unpair.1)) paths.pred.unpair.2

theorem betaTraceTickCode_eval (state : Nat) :
    betaTraceTickCode.eval state = Part.some (betaTraceTickValue state) := by
  let current := state.unpair.1
  let paths := state.unpair.2
  have hc : Code.eval .left state = Part.some current := rfl
  have hp : Code.eval .right state = Part.some paths := rfl
  have hz : Code.eval .zero state = Part.some 0 := rfl
  have hpredc := evalCompSome predCode .left _ _ _ hc (eval_predCode current)
  have hpredp := evalCompSome predCode .right _ _ _ hp (eval_predCode paths)
  have hhead := evalCompSome .left (.comp predCode .right) _ _ _ hpredp
    (show Code.eval .left paths.pred = Part.some paths.pred.unpair.1 from rfl)
  have htail := evalCompSome .right (.comp predCode .right) _ _ _ hpredp
    (show Code.eval .right paths.pred = Part.some paths.pred.unpair.2 from rfl)
  have happlyarg := evalPairSome (.comp predCode .left) betaTraceHeadCode _ _ _ hpredc hhead
  have happly := evalCompSome betaAtPathCode _ _ _ _ happlyarg
    (betaAtPathCode_any current.pred paths.pred.unpair.1)
  have hnext := chooseZeroCode_eval .left .zero betaTraceApplyCode _ _ _ _ hc hz happly
  have hnexttail := evalPairSome betaTraceNextCode betaTraceTailCode _ _ _ hnext htail
  have hresult := chooseZeroCode_eval .right Code.id (.pair betaTraceNextCode betaTraceTailCode)
    _ _ _ _ hp (Code.eval_id state) hnexttail
  simpa [betaTraceTickCode, betaTraceNextCode, betaTraceApplyCode, betaTraceHeadCode,
    betaTraceTailCode, betaTraceTickValue, current, paths] using hresult

def encodeBetaTrace (current : Option Term) (paths : List (List Bool)) : Nat :=
  Nat.pair (Encodable.encode (current.map directTermNumber)) (Encodable.encode paths)

theorem betaTraceTickValue_correct (current : Option Term) (paths : List (List Bool)) :
    betaTraceTickValue (encodeBetaTrace current paths) =
      encodeBetaTrace (betaTrace 1 current paths).1 (betaTrace 1 current paths).2 := by
  cases paths with
  | nil => simp [betaTraceTickValue, encodeBetaTrace, betaTrace]
  | cons path paths =>
    cases current with
    | none => simp [betaTraceTickValue, encodeBetaTrace, betaTrace, Encodable.encode_list_cons]
    | some t =>
      simp [betaTraceTickValue, encodeBetaTrace, betaTrace, Encodable.encode_list_cons,
        betaPathValue_correct]

def betaTraceIterValue : Nat → Nat → Nat
  | 0, state => state
  | fuel + 1, state => betaTraceIterValue fuel (betaTraceTickValue state)

theorem betaTraceIterValue_comm (fuel state : Nat) :
    betaTraceTickValue (betaTraceIterValue fuel state) =
      betaTraceIterValue fuel (betaTraceTickValue state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih => simpa [betaTraceIterValue] using ih (betaTraceTickValue state)

theorem betaTraceIterCode_eval (state fuel : Nat) :
    betaTraceIterCode.eval (Nat.pair state fuel) = Part.some (betaTraceIterValue fuel state) := by
  induction fuel with
  | zero =>
    rw [betaTraceIterCode, Code.eval_prec_zero]
    exact Code.eval_id state
  | succ fuel ih =>
    rw [betaTraceIterCode, Code.eval_prec_succ]
    change (betaTraceIterCode.eval (Nat.pair state fuel)).bind _ = _
    rw [ih, Part.bind_some]
    have hp : Code.eval (.comp .right .right) (Nat.pair state (Nat.pair fuel (betaTraceIterValue fuel state))) =
        Part.some (betaTraceIterValue fuel state) := by
      change (Code.eval .right _).bind (fun z => Code.eval .right z) = _
      simp [Code.eval, Part.bind_some]
    have hs := evalCompSome betaTraceTickCode (.comp .right .right) _ _ _ hp
      (betaTraceTickCode_eval (betaTraceIterValue fuel state))
    rw [betaTraceIterValue_comm] at hs
    exact hs

theorem betaTraceIterValue_correct (fuel : Nat) (current : Option Term) (paths : List (List Bool)) :
    betaTraceIterValue fuel (encodeBetaTrace current paths) =
      encodeBetaTrace (betaTrace fuel current paths).1 (betaTrace fuel current paths).2 := by
  induction fuel generalizing current paths with
  | zero => rfl
  | succ fuel ih =>
    rw [betaTraceIterValue, betaTraceTickValue_correct]
    cases paths with
    | nil => simpa [betaTrace] using ih current []
    | cons path paths => simpa [betaTrace] using ih (current.bind (betaAtPath path)) paths

theorem betaTraceIterCode_correct (fuel : Nat) (current : Option Term) (paths : List (List Bool)) :
    betaTraceIterCode.eval (Nat.pair (encodeBetaTrace current paths) fuel) =
      Part.some (encodeBetaTrace (betaTrace fuel current paths).1 (betaTrace fuel current paths).2) := by
  rw [betaTraceIterCode_eval, betaTraceIterValue_correct]

def betaCertificateRunCode : Code := .comp .left
  (.comp betaTraceIterCode (.pair (.pair (.comp .succ .left) .right) .right))

theorem betaCertificateRunCode_eval (t : Term) (paths : List (List Bool)) :
    betaCertificateRunCode.eval (Nat.pair (directTermNumber t) (Encodable.encode paths)) =
      Part.some (Encodable.encode ((betaRun paths t).map directTermNumber)) := by
  let input := Nat.pair (directTermNumber t) (Encodable.encode paths)
  have ht : Code.eval .left input = Part.some (directTermNumber t) := by simp [input, Code.eval]
  have hp : Code.eval .right input = Part.some (Encodable.encode paths) := by simp [input, Code.eval]
  have ht' := evalCompSome .succ .left _ _ _ ht
    (show Code.eval .succ (directTermNumber t) = Part.some (directTermNumber t + 1) from rfl)
  have hstate := evalPairSome (.comp .succ .left) .right _ _ _ ht' hp
  have harg := evalPairSome (.pair (.comp .succ .left) .right) .right _ _ _ hstate hp
  have hrun := betaTraceIterCode_correct (Encodable.encode paths) (some t) paths
  rw [betaTrace_encoded_fuel] at hrun
  have hrun' : betaTraceIterCode.eval
      (Nat.pair (Nat.pair (directTermNumber t + 1) (Encodable.encode paths)) (Encodable.encode paths)) =
      Part.some (Nat.pair (Encodable.encode ((betaRun paths t).map directTermNumber)) 0) := by
    simpa [encodeBetaTrace] using hrun
  have hiter := evalCompSome betaTraceIterCode _ _ _ _ harg hrun'
  have hresult := evalCompSome .left _ _ _ _ hiter
    (show Code.eval .left (Nat.pair (Encodable.encode ((betaRun paths t).map directTermNumber)) 0) =
      Part.some (Encodable.encode ((betaRun paths t).map directTermNumber)) from by simp [Code.eval])
  exact hresult

#print axioms betaTraceTickCode
#print axioms betaTraceIterCode
#print axioms betaTraceTickCode_eval
#print axioms betaTraceIterCode_correct
#print axioms betaCertificateRunCode
#print axioms betaCertificateRunCode_eval
end LambdaTuring
