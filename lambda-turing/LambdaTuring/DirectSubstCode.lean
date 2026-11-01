/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectSubstReference
public meta import LambdaTuring.DirectSubstReference

@[expose] public section

namespace LambdaTuring
open Nat.Partrec
open LambdaTuring.Machine
open LambdaTuring.EffectiveCode

structure SubstStepRep (f : Nat → Nat → List Nat → Nat) where
  code : Code
  sound : ∀ value key history,
    code.eval (Nat.pair value (Nat.pair key (Encodable.encode history))) = Part.some (f value key history)

def SubstStepRep.fromLift {f : Nat → List Nat → Nat} (r : LiftStepRep f) :
    SubstStepRep (fun _ key history => f key history) := ⟨r.code, r.sound⟩

def SubstStepRep.map (op : Code) (g : Nat → Nat) (hg : ∀ n, op.eval n = Part.some (g n))
    {f : Nat → Nat → List Nat → Nat} (r : SubstStepRep f) : SubstStepRep (fun v k h => g (f v k h)) :=
  ⟨.comp op r.code, fun value key history => evalCompSome op r.code _ _ _
    (r.sound value key history) (hg (f value key history))⟩

def SubstStepRep.pair {f g : Nat → Nat → List Nat → Nat} (rf : SubstStepRep f) (rg : SubstStepRep g) :
    SubstStepRep (fun v k h => Nat.pair (f v k h) (g v k h)) :=
  ⟨.pair rf.code rg.code, fun value key history => evalPairSome rf.code rg.code _ _ _
    (rf.sound value key history) (rg.sound value key history)⟩

def SubstStepRep.select {test yes no : Nat → Nat → List Nat → Nat}
    (rt : SubstStepRep test) (ry : SubstStepRep yes) (rn : SubstStepRep no) :
    SubstStepRep (fun v k h => if test v k h = 0 then yes v k h else no v k h) :=
  ⟨chooseZeroCode rt.code ry.code rn.code, fun value key history =>
    chooseZeroCode_eval rt.code ry.code rn.code _ _ _ _
      (rt.sound value key history) (ry.sound value key history) (rn.sound value key history)⟩

def substContextRep : SubstStepRep (fun value _ _ => value) := by
  refine ⟨.left, ?_⟩
  intro value key history
  simp [Code.eval]

def substTermRep := SubstStepRep.fromLift liftTermRep
def substDepthRep := SubstStepRep.fromLift liftDepthRep
def substTagRep := SubstStepRep.fromLift liftTagRep
def substPayloadRep := SubstStepRep.fromLift liftPayloadRep
def substAbsRep := SubstStepRep.fromLift liftAbstractionRep
def substAppRep := SubstStepRep.fromLift liftApplicationRep

def substSubRep {f g : Nat → Nat → List Nat → Nat} (rf : SubstStepRep f) (rg : SubstStepRep g) :
    SubstStepRep (fun v k h => f v k h - g v k h) := by
  refine ⟨.comp subPairCode (.pair rf.code rg.code), ?_⟩
  intro value key history
  have hp := evalPairSome rf.code rg.code _ _ _ (rf.sound value key history) (rg.sound value key history)
  exact evalCompSome subPairCode _ _ _ _ hp (subPairCode_eval (f value key history) (g value key history))

def substEqualRep {f g : Nat → Nat → List Nat → Nat} (rf : SubstStepRep f) (rg : SubstStepRep g) :
    SubstStepRep (fun v k h => if f v k h = g v k h then 1 else 0) := by
  refine ⟨.comp equalNatCode (.pair rf.code rg.code), ?_⟩
  intro value key history
  have hp := evalPairSome rf.code rg.code _ _ _ (rf.sound value key history) (rg.sound value key history)
  exact evalCompSome equalNatCode _ _ _ _ hp (equalNatCode_eval (f value key history) (g value key history))

def substVarRep {f : Nat → Nat → List Nat → Nat} (r : SubstStepRep f) :
    SubstStepRep (fun v k h => directVarNumber (f v k h)) :=
  r.map directVarCode directVarNumber (fun n => directTaggedCode_eval 0 n)

def substPredRep {f : Nat → Nat → List Nat → Nat} (r : SubstStepRep f) :
    SubstStepRep (fun v k h => (f v k h).pred) := r.map predCode Nat.pred eval_predCode

def substLiftByRep : SubstStepRep (fun value key _ => liftByValue key.unpair.2 value) := by
  refine ⟨.comp directLiftByCode (.pair substContextRep.code substDepthRep.code), ?_⟩
  intro value key history
  have hp := evalPairSome substContextRep.code substDepthRep.code _ _ _
    (substContextRep.sound value key history) (substDepthRep.sound value key history)
  exact evalCompSome directLiftByCode _ _ _ _ hp (directLiftByCode_any value key.unpair.2)

def substVariableRep := (substEqualRep substPayloadRep substDepthRep).select
  ((substSubRep substPayloadRep substDepthRep).select (substVarRep substPayloadRep)
    (substVarRep (substPredRep substPayloadRep))) substLiftByRep
def substTagDispatchRep := substTagRep.select substVariableRep
  ((substPredRep substTagRep).select substAbsRep
    ((substPredRep (substPredRep substTagRep)).select substAppRep substTermRep))
def substStepRep := (substSubRep substTermRep substDepthRep).select substTermRep substTagDispatchRep

def substVariableCode : Code := chooseZeroCode
  (.comp equalNatCode (.pair liftPayloadCode liftDepthCode))
  (chooseZeroCode (liftSubCode liftPayloadCode liftDepthCode) (.comp directVarCode liftPayloadCode)
    (.comp directVarCode (.comp predCode liftPayloadCode)))
  (.comp directLiftByCode (.pair .left liftDepthCode))
def substTagDispatchCode : Code := chooseZeroCode liftTagCode substVariableCode
  (chooseZeroCode (.comp predCode liftTagCode) liftAbstractionCode
    (chooseZeroCode (.comp predCode (.comp predCode liftTagCode)) liftApplicationCode liftTermCode))
def substStepCode : Code := chooseZeroCode (liftSubCode liftTermCode liftDepthCode) liftTermCode substTagDispatchCode

theorem substStepRep_code : substStepRep.code = substStepCode := rfl

def substStepFormula (value key : Nat) (history : List Nat) : Nat :=
  let term := key.unpair.1
  let depth := key.unpair.2
  let tag := directTag term
  let data := directPayload term
  let readChild := fun child d => if child - d = 0 then child else
    (history[key.pred - Nat.pair child d]?).getD 0
  if term - depth = 0 then term
  else if tag = 0 then
    if (if data = depth then 1 else 0) = 0 then
      (if data - depth = 0 then directVarNumber data else directVarNumber data.pred)
    else liftByValue depth value
  else if tag.pred = 0 then directAbsNumber (readChild data (depth + 1))
  else if tag.pred.pred = 0 then directAppNumber
    (readChild data.unpair.1 depth) (readChild data.unpair.2 depth)
  else term

theorem substStepFormula_eq (value key : Nat) (history : List Nat) :
    substStepFormula value key history = substStepValue value key history := by
  simp only [substStepFormula, substStepValue, liftChildValue, liftHistoryRead,
    Nat.sub_eq_zero_iff_le, Nat.pred_eq_sub_one]
  split_ifs <;> simp_all <;> omega

theorem substStepCode_eval (value key : Nat) (history : List Nat) :
    substStepCode.eval (Nat.pair value (Nat.pair key (Encodable.encode history))) =
      Part.some (substStepValue value key history) := by
  have h := substStepRep.sound value key history
  rw [substStepRep_code] at h
  change substStepCode.eval (Nat.pair value (Nat.pair key (Encodable.encode history))) =
      Part.some (substStepFormula value key history) at h
  rw [substStepFormula_eq] at h
  exact h

def directSubstCode : Code := courseCode substStepCode

theorem directSubstCode_any (value key : Nat) :
    directSubstCode.eval (Nat.pair value key) = Part.some (substValue value key) := by
  have hstep : ∀ v key,
      substStepCode.eval (Nat.pair v (Nat.pair key (Encodable.encode (courseHistory substValue v key)))) =
        Part.some (substValue v key) := by
    intro v key
    rw [substHistory_eq_course, substStepCode_eval]
    rfl
  exact courseCode_eval substStepCode substValue hstep value key

theorem directSubstCode_eval (t value : Term) (depth : Nat) :
    directSubstCode.eval (Nat.pair (directTermNumber value) (Nat.pair (directTermNumber t) depth)) =
      Part.some (directTermNumber (substAt depth value t)) := by
  rw [directSubstCode_any, substValue_correct]

#print axioms substStepCode
#print axioms directSubstCode
#print axioms directSubstCode_eval
end LambdaTuring
