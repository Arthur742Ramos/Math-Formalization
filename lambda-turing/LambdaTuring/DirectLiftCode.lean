/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectLiftReference
public meta import LambdaTuring.DirectLiftReference

@[expose] public section

namespace LambdaTuring
open Nat.Partrec
open LambdaTuring.Machine
open LambdaTuring.EffectiveCode

theorem historyLookupCode_any (k j : Nat) (history : List Nat) :
    historyLookupCode.eval (Nat.pair (Nat.pair k j) (Encodable.encode history)) =
      Part.some ((history[k.pred - j]?).getD 0) := by
  let input := Nat.pair (Nat.pair k j) (Encodable.encode history)
  have hl : Code.eval .left input = Part.some (Nat.pair k j) := by simp [input, Code.eval]
  have hr : Code.eval .right input = Part.some (Encodable.encode history) := by simp [input, Code.eval]
  have hk' : Code.eval .left (Nat.pair k j) = Part.some k := by simp [Code.eval]
  have hj' : Code.eval .right (Nat.pair k j) = Part.some j := by simp [Code.eval]
  have hk := evalCompSome .left .left _ _ _ hl hk'
  have hj := evalCompSome .right .left _ _ _ hl hj'
  have hpred := evalCompSome predCode (.comp .left .left) _ _ _ hk (eval_predCode k)
  have hindexInput := evalPairSome (.comp predCode (.comp .left .left)) (.comp .right .left) _ _ _ hpred hj
  have hindex := evalCompSome subPairCode _ _ _ _ hindexInput (subPairCode_eval k.pred j)
  have hlookupInput := evalPairSome .right historyIndexCode _ _ _ hr hindex
  have hlookup := evalCompSome listLookupCode _ _ _ _ hlookupInput (listLookupCode_eval history (k.pred - j))
  have hvalue := evalCompSome predCode _ _ _ _ hlookup (eval_predCode (Encodable.encode history[k.pred - j]?))
  cases he : history[k.pred - j]? with
  | none =>
    rw [he] at hvalue
    simpa [historyLookupCode, historyIndexCode, input, he] using hvalue
  | some n =>
    rw [he] at hvalue
    simpa [historyLookupCode, historyIndexCode, input, he] using hvalue

/-- A numerical code whose behavior is proved on a valid encoded history. -/
structure LiftStepRep (f : Nat → List Nat → Nat) where
  code : Code
  sound : ∀ context key history,
    code.eval (Nat.pair context (Nat.pair key (Encodable.encode history))) = Part.some (f key history)

def LiftStepRep.map (op : Code) (g : Nat → Nat) (hg : ∀ n, op.eval n = Part.some (g n))
    {f : Nat → List Nat → Nat} (r : LiftStepRep f) : LiftStepRep (fun k h => g (f k h)) :=
  ⟨.comp op r.code, fun context key history => evalCompSome op r.code _ _ _
    (r.sound context key history) (hg (f key history))⟩

def LiftStepRep.pair {f g : Nat → List Nat → Nat} (rf : LiftStepRep f) (rg : LiftStepRep g) :
    LiftStepRep (fun k h => Nat.pair (f k h) (g k h)) :=
  ⟨.pair rf.code rg.code, fun context key history => evalPairSome rf.code rg.code _ _ _
    (rf.sound context key history) (rg.sound context key history)⟩

def LiftStepRep.select {test yes no : Nat → List Nat → Nat}
    (rt : LiftStepRep test) (ry : LiftStepRep yes) (rn : LiftStepRep no) :
    LiftStepRep (fun k h => if test k h = 0 then yes k h else no k h) :=
  ⟨chooseZeroCode rt.code ry.code rn.code, fun context key history =>
    chooseZeroCode_eval rt.code ry.code rn.code _ _ _ _
      (rt.sound context key history) (ry.sound context key history) (rn.sound context key history)⟩

def liftKeyRep : LiftStepRep (fun k _ => k) := by
  refine ⟨.comp .left .right, ?_⟩
  intro context key history
  change (Code.eval .right _).bind (fun z => Code.eval .left z) = _
  simp [Code.eval, Part.bind_some]

def liftHistoryRep : LiftStepRep (fun _ h => Encodable.encode h) := by
  refine ⟨.comp .right .right, ?_⟩
  intro context key history
  change (Code.eval .right _).bind (fun z => Code.eval .right z) = _
  simp [Code.eval, Part.bind_some]

def LiftStepRep.lookup {f g : Nat → List Nat → Nat} (rk : LiftStepRep f) (rj : LiftStepRep g) :
    LiftStepRep (fun k h => (h[(f k h).pred - g k h]?).getD 0) := by
  let arg := (rk.pair rj).pair liftHistoryRep
  refine ⟨.comp historyLookupCode arg.code, ?_⟩
  intro context key history
  exact evalCompSome historyLookupCode arg.code _ _ _ (arg.sound context key history)
    (historyLookupCode_any (f key history) (g key history) history)

def liftLeftRep {f : Nat → List Nat → Nat} (r : LiftStepRep f) :
    LiftStepRep (fun k h => (f k h).unpair.1) :=
  r.map .left (fun n => n.unpair.1) (fun _ => rfl)

def liftRightRep {f : Nat → List Nat → Nat} (r : LiftStepRep f) :
    LiftStepRep (fun k h => (f k h).unpair.2) :=
  r.map .right (fun n => n.unpair.2) (fun _ => rfl)

def liftPredRep {f : Nat → List Nat → Nat} (r : LiftStepRep f) :
    LiftStepRep (fun k h => (f k h).pred) := r.map predCode Nat.pred eval_predCode

def liftSuccRep {f : Nat → List Nat → Nat} (r : LiftStepRep f) :
    LiftStepRep (fun k h => f k h + 1) := r.map .succ Nat.succ (fun _ => rfl)

def liftSubRep {f g : Nat → List Nat → Nat} (rf : LiftStepRep f) (rg : LiftStepRep g) :
    LiftStepRep (fun k h => f k h - g k h) := by
  refine ⟨.comp subPairCode (.pair rf.code rg.code), ?_⟩
  intro context key history
  have hp := evalPairSome rf.code rg.code _ _ _ (rf.sound context key history) (rg.sound context key history)
  exact evalCompSome subPairCode _ _ _ _ hp (subPairCode_eval (f key history) (g key history))

def liftVarRep {f : Nat → List Nat → Nat} (r : LiftStepRep f) :
    LiftStepRep (fun k h => directVarNumber (f k h)) :=
  r.map directVarCode directVarNumber (fun n => directTaggedCode_eval 0 n)

def liftAbsRep {f : Nat → List Nat → Nat} (r : LiftStepRep f) :
    LiftStepRep (fun k h => directAbsNumber (f k h)) :=
  r.map directAbsCode directAbsNumber (fun n => directTaggedCode_eval 1 n)

def liftAppRep {f g : Nat → List Nat → Nat} (rf : LiftStepRep f) (rg : LiftStepRep g) :
    LiftStepRep (fun k h => directAppNumber (f k h) (g k h)) := by
  refine ⟨.comp directAppCode (.pair rf.code rg.code), ?_⟩
  intro context key history
  have hp := evalPairSome rf.code rg.code _ _ _ (rf.sound context key history) (rg.sound context key history)
  exact evalCompSome directAppCode _ _ _ _ hp (directTaggedCode_eval 2 (Nat.pair (f key history) (g key history)))

def liftTermRep : LiftStepRep (fun k _ => k.unpair.1) := liftLeftRep liftKeyRep
def liftDepthRep : LiftStepRep (fun k _ => k.unpair.2) := liftRightRep liftKeyRep
def liftTagRep : LiftStepRep (fun k _ => directTag k.unpair.1) := liftLeftRep (liftPredRep liftTermRep)
def liftPayloadRep : LiftStepRep (fun k _ => directPayload k.unpair.1) := liftRightRep (liftPredRep liftTermRep)
def liftLeftChildRep := liftLeftRep liftPayloadRep
def liftRightChildRep := liftRightRep liftPayloadRep

def liftSafeChildRep {f g : Nat → List Nat → Nat} (child : LiftStepRep f) (depth : LiftStepRep g) :
    LiftStepRep (fun k h => if f k h - g k h = 0 then f k h else
      (h[k.pred - Nat.pair (f k h) (g k h)]?).getD 0) :=
  (liftSubRep child depth).select child (LiftStepRep.lookup liftKeyRep (child.pair depth))

def liftVariableRep := (liftSubRep liftDepthRep liftPayloadRep).select
  (liftVarRep (liftSuccRep liftPayloadRep)) (liftVarRep liftPayloadRep)
def liftAbstractionRep := liftAbsRep (liftSafeChildRep liftPayloadRep (liftSuccRep liftDepthRep))
def liftApplicationRep := liftAppRep (liftSafeChildRep liftLeftChildRep liftDepthRep)
  (liftSafeChildRep liftRightChildRep liftDepthRep)
def liftTagDispatchRep := liftTagRep.select liftVariableRep
  ((liftPredRep liftTagRep).select liftAbstractionRep
    ((liftPredRep (liftPredRep liftTagRep)).select liftApplicationRep liftTermRep))
def liftStepRep := (liftSubRep liftTermRep liftDepthRep).select liftTermRep liftTagDispatchRep

def liftKeyCode : Code := .comp .left .right
def liftHistoryCode : Code := .comp .right .right
def liftTermCode : Code := .comp .left liftKeyCode
def liftDepthCode : Code := .comp .right liftKeyCode
def liftTagCode : Code := .comp .left (.comp predCode liftTermCode)
def liftPayloadCode : Code := .comp .right (.comp predCode liftTermCode)
def liftSubCode (a b : Code) : Code := .comp subPairCode (.pair a b)
def liftSafeChildCode (child depth : Code) : Code :=
  chooseZeroCode (liftSubCode child depth) child
    (.comp historyLookupCode (.pair (.pair liftKeyCode (.pair child depth)) liftHistoryCode))
def liftVariableCode : Code := chooseZeroCode (liftSubCode liftDepthCode liftPayloadCode)
  (.comp directVarCode (.comp .succ liftPayloadCode)) (.comp directVarCode liftPayloadCode)
def liftAbstractionCode : Code := .comp directAbsCode
  (liftSafeChildCode liftPayloadCode (.comp .succ liftDepthCode))
def liftApplicationCode : Code := .comp directAppCode
  (.pair (liftSafeChildCode (.comp .left liftPayloadCode) liftDepthCode)
    (liftSafeChildCode (.comp .right liftPayloadCode) liftDepthCode))
def liftTagDispatchCode : Code := chooseZeroCode liftTagCode liftVariableCode
  (chooseZeroCode (.comp predCode liftTagCode) liftAbstractionCode
    (chooseZeroCode (.comp predCode (.comp predCode liftTagCode)) liftApplicationCode liftTermCode))
def liftStepCode : Code := chooseZeroCode (liftSubCode liftTermCode liftDepthCode) liftTermCode liftTagDispatchCode

theorem liftStepRep_code : liftStepRep.code = liftStepCode := rfl

def liftStepFormula (key : Nat) (history : List Nat) : Nat :=
  let term := key.unpair.1
  let depth := key.unpair.2
  let tag := directTag term
  let data := directPayload term
  let readChild := fun child d => if child - d = 0 then child else
    (history[key.pred - Nat.pair child d]?).getD 0
  if term - depth = 0 then term
  else if tag = 0 then
    if depth - data = 0 then directVarNumber (data + 1) else directVarNumber data
  else if tag.pred = 0 then directAbsNumber (readChild data (depth + 1))
  else if tag.pred.pred = 0 then directAppNumber
    (readChild data.unpair.1 depth) (readChild data.unpair.2 depth)
  else term

theorem liftStepFormula_eq (key : Nat) (history : List Nat) :
    liftStepFormula key history = liftStepValue key history := by
  simp only [liftStepFormula, liftStepValue, liftChildValue, liftHistoryRead,
    Nat.sub_eq_zero_iff_le, Nat.pred_eq_sub_one]
  split_ifs <;> simp_all <;> omega

theorem liftStepCode_eval (context key : Nat) (history : List Nat) :
    liftStepCode.eval (Nat.pair context (Nat.pair key (Encodable.encode history))) =
      Part.some (liftStepValue key history) := by
  have h := liftStepRep.sound context key history
  rw [liftStepRep_code] at h
  change liftStepCode.eval (Nat.pair context (Nat.pair key (Encodable.encode history))) =
      Part.some (liftStepFormula key history) at h
  rw [liftStepFormula_eq] at h
  exact h

/-- Capture-avoiding lifting on a direct term code and a cutoff. -/
def directLiftCode : Code := .comp (courseCode liftStepCode) (.pair .zero Code.id)

theorem directLiftCode_any (term depth : Nat) :
    directLiftCode.eval (Nat.pair term depth) = Part.some (liftValue (Nat.pair term depth)) := by
  have hstep : ∀ context key,
      liftStepCode.eval (Nat.pair context
        (Nat.pair key (Encodable.encode (courseHistory (fun _ k => liftValue k) context key)))) =
          Part.some (liftValue key) := by
    intro context key
    rw [liftHistory_eq_course, liftStepCode_eval]
    rfl
  let input := Nat.pair term depth
  have hz : Code.eval .zero input = Part.some 0 := rfl
  have hp := evalPairSome .zero Code.id input 0 input hz (Code.eval_id input)
  have hcourse := courseCode_eval liftStepCode (fun _ key => liftValue key) hstep 0 input
  have h := evalCompSome (courseCode liftStepCode) (.pair .zero Code.id) _ _ _ hp hcourse
  exact h

theorem directLiftCode_eval (t : Term) (depth : Nat) :
    directLiftCode.eval (Nat.pair (directTermNumber t) depth) =
      Part.some (directTermNumber (liftFrom depth t)) := by
  rw [directLiftCode_any, liftValue_correct]

#print axioms historyLookupCode_any
#print axioms liftStepCode
#print axioms liftStepCode_eval
#print axioms directLiftCode
#print axioms directLiftCode_eval
end LambdaTuring
